import hashlib
import sqlite3
from datetime import datetime
from enum import Enum
from typing import Optional

from pyservice import ServiceException


class MsgqErrorCode(Enum):
    """
    Represents the error codes for the message queue service.
    """
    DATABASE_CONSTRAINT = 'ERROR_DATABASE_CONSTRAINT'
    MSGQ_STATE = 'ERROR_MSGQ_STATE'


class DatabaseConstraintException(ServiceException):
    """
    Indicates a database constraint has been violated.

    :param inner: The inner exception.
    :type inner: Exception
    """

    def __init__(self, inner: Exception):
        super(DatabaseConstraintException, self).__init__(MsgqErrorCode.DATABASE_CONSTRAINT,
                                                          f'database constraint violated: {inner}')
        self.inner = inner


class StateException(ServiceException):
    """
    Indicates the state of the queue is invalid.

    """

    def __init__(self, message: str):
        super(StateException, self).__init__(MsgqErrorCode.MSGQ_STATE, message)


class QueueName:
    """
    Represents a valid queue name.

    :param name: The name of the queue.
    :type name: str
    """

    VALID_CHARACTERS = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-'

    def __init__(self, name: str):
        self.name = name

    def __str__(self) -> str:
        """
        Converts the queue name to a string.

        Returns:
            A string containing the queue name.
        """
        return self.name

    @staticmethod
    def validated(queue_name: str) -> 'QueueName':
        """
        Validates the given string as the name of a queue.  Checks the
        string against characters in VALID_CHARACTERS.

        :param queue_name: The name of the queue to validate.
        :type queue_name: str
        :return: A QueueName instance.
        :rtype: QueueName
        :raises ValueError: The queue name is invalid.
        """
        for character in queue_name:
            if character not in QueueName.VALID_CHARACTERS:
                raise ValueError(
                    f'Invalid queue name: {queue_name}. Must consist of characters in [{QueueName.VALID_CHARACTERS}]')
            else:
                pass
        return QueueName(queue_name)


class ChecksumID:
    """
    Represents a checksum ID.  You can create an instance of this class
    by passing in the message payload, or by passing in the hex digest
    of the checksum.

    :param payload: The message payload.
    :type payload: bytes
    :param hexdigest: The hex digest of the checksum.
    :type hexdigest: str
    :raises ValueError: Either payload or hexdigest must be specified, but not both.
    """

    def __init__(self, payload: Optional[bytes] = None, hexdigest: Optional[str] = None):
        if payload is not None and hexdigest is None:
            sha256 = hashlib.sha256(payload, usedforsecurity=False)
            self.sha256_digest = sha256.hexdigest()
        elif payload is None and hexdigest is not None:
            self.sha256_digest = hexdigest
        else:
            raise ValueError(
                'Either payload or hexdigest must be specified, but not both.')

    def __str__(self) -> str:
        """
        Returns the checksum in hex digest.

        Returns:
            A string containing the checksum ID.
        """
        return self.sha256_digest


class Status(Enum):
    """
    Represents the status of a message in the queue.
    """
    QUEUED = 1
    PROCESSING = 2
    ARCHIVED = 3
    ABANDONED = 4
    CANCELLED = 5

    @staticmethod
    def create_table(conn: sqlite3.Connection) -> None:
        """
        Creates the status table in the database.

        :param conn: The database connection.
        :type conn: sqlite3.Connection
        """
        conn.execute('''CREATE TABLE IF NOT EXISTS status
                        (id INTEGER PRIMARY KEY,
                         name TEXT NOT NULL)''')
        for status in Status:
            conn.execute(
                '''INSERT OR IGNORE INTO status (id, name)
                   VALUES (?, ?)''', (status.value, status.name))


class MessageQueue:
    """
    Represents a persistent message queue.

    :param path: The path to the directory where the queue database will
                 be stored.
    :type path: str
    :param name: The name of the queue.
    :type name: QueueName
    """

    def __init__(self: 'MessageQueue', path: str, name: QueueName):
        self.db_path = f'{path}/{name}.db'
        with sqlite3.connect(self.db_path) as conn:
            Status.create_table(conn)
            conn.execute('''CREATE TABLE IF NOT EXISTS msgq
                            (csid TEXT PRIMARY KEY,
                             payload BLOB NOT NULL,
                             status_id INTEGER NOT NULL,
                             when_pushed DATETIME NOT NULL,
                             when_deleted DATETIME,
                             when_delivered DATETIME,
                             when_error DATETIME,
                             num_attempts INTEGER NOT NULL DEFAULT 0,
                             last_error TEXT,
                             FOREIGN KEY (status_id) REFERENCES status(id))''')

    def push(self: 'MessageQueue', payload: bytes) -> None:
        """
        Pushes a message onto the queue.

        :param payload: The message payload.
        :type payload: bytes
        :raises DatabaseConstraintException: The message already exists in
                                             the queue.
        """
        with sqlite3.connect(self.db_path) as conn:
            when_pushed = datetime.now()
            csid = ChecksumID(payload)
            cursor = conn.cursor()
            try:
                cursor.execute(
                    '''INSERT INTO msgq (csid, payload, status_id, when_pushed)
                            VALUES (?, ?, ?, ?)''',
                    (str(csid), payload, Status.QUEUED.value, when_pushed))
            except sqlite3.IntegrityError as e:
                raise DatabaseConstraintException(e)

    def process(self) -> Optional[tuple[ChecksumID, bytes]]:
        """
        Returns the next message to process.  If there is already a
        message being processed, it will return that message.  If there
        are no messages being processed, it will return the next
        message in the queue.  If there are no messages in the queue,
        it will return None.

        :return: A tuple containing the checksum ID and payload of the
                 next message to process, or None if there are no
                 messages to process.
        :rtype: Optional[tuple[ChecksumID, bytes]]
        """
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute(
                '''SELECT csid, payload, status_id, when_pushed, when_error FROM msgq
                    WHERE when_deleted IS NULL AND status_id in (?, ?)
                    ORDER BY status_id desc,
                        CASE WHEN when_error IS NULL THEN when_pushed ELSE when_error END''',
                (Status.PROCESSING.value, Status.QUEUED.value))
            row = cursor.fetchone()
            if row is not None:
                csid = ChecksumID(hexdigest=row[0])
                if row[2] != Status.PROCESSING.value:
                    MessageQueue.__update_status(
                        conn, csid, Status.PROCESSING)
                    return (csid, row[1])
                else:
                    return (csid, row[1])
            else:
                return None

    def archive(self, csid: ChecksumID) -> None:
        """
        Archives a message.  The queue controller has succeeded delivering
        this message.

        :param csid: The ID of the message to archive.
        :type csid: ChecksumID
        :raises StateException: No message is in the PROCESSING status.
        """
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute('UPDATE msgq SET status_id=? WHERE when_deleted IS NULL AND csid=? AND status_id=?',
                           (Status.ARCHIVED.value, str(csid), Status.PROCESSING.value))
            if cursor.rowcount < 1:
                raise StateException(
                    f'No message with ID [{csid}] found in PROCESSING status.')
            else:
                pass

    def fail(self, csid: ChecksumID, reason: str) -> None:
        """
        Fails a message.  The queue controller has failed delivering
        this message.

        :param csid: The ID of the message to fail.
        :type csid: ChecksumID
        :param reason: The reason for failure.
        :type reason: str
        :raises StateException: No message is in the PROCESSING status.
        """
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute('''UPDATE msgq
                            SET status_id=?, last_error=?, when_error=datetime(\'now\'), num_attempts=num_attempts+1
                            WHERE when_deleted IS NULL AND csid=? AND status_id=?''',
                           (Status.QUEUED.value, reason, str(csid), Status.PROCESSING.value))
            if cursor.rowcount < 1:
                raise StateException(
                    f'No message with ID [{csid}] found in PROCESSING status.')
            else:
                pass

    def update_task_status(self, task_id: int, status: str):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute(
                '''UPDATE tasks SET status=? WHERE id=?''', (status, task_id))

    def update_task_last_run(self, task_id: int, timestamp: int):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute(
                '''UPDATE tasks SET last_run=? WHERE id=?''', (timestamp, task_id))

    def update_task_num_retries(self, task_id: int, num_retries: int):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute(
                '''UPDATE tasks SET num_retries=? WHERE id=?''', (num_retries, task_id))

    def update_task_last_result(self, task_id: int, result: str):
        with sqlite3.connect(self.db_path) as conn:
            conn.execute(
                '''UPDATE tasks SET last_result=? WHERE id=?''', (result, task_id))

    @staticmethod
    def __update_status(conn: sqlite3.Connection, csid: ChecksumID, status: Status) -> None:
        conn.execute(
            '''UPDATE msgq SET status_id=? WHERE when_deleted IS NULL AND csid=?''', (status.value, str(csid)))
