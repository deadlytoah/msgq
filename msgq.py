#
# Persistent Message Queue Service
# Copyright (C) 2023  Hee Shin
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.
#

import hashlib
import json
import sqlite3
from dataclasses import dataclass
from datetime import datetime
from enum import Enum
from typing import List, Optional

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


@dataclass
class Message:
    """
    Represents a message in the queue.

    :param csid: The checksum ID of the message.
    :type csid: ChecksumID
    :param payload: The message payload.
    :type payload: bytes
    :param status: The status of the message.
    :type status: Status
    :param when_pushed: The date/time the message was pushed onto the queue.
    :type when_pushed: datetime
    :param when_deleted: The date/time the message was deleted from the queue.
    :type when_deleted: datetime
    :param when_delivered: The date/time the message was delivered.
    :type when_delivered: datetime
    :param when_error: The date/time the message encountered an error.
    :type when_error: datetime
    :param num_attempts: The number of times the message has been attempted.
    :type num_attempts: int
    :param last_error: The last error that occurred.
    :type last_error: str
    """

    csid: ChecksumID
    payload: bytes
    status: Status
    when_pushed: datetime
    when_deleted: Optional[datetime]
    when_delivered: Optional[datetime]
    when_error: Optional[datetime]
    num_attempts: int
    last_error: Optional[str]

    def as_json(self) -> str:
        """
        Returns the message as a JSON string.

        :return: A JSON representing the message.
        :rtype: str
        """
        assert isinstance(self.when_pushed, datetime)
        dictionary = {
            'csid': str(self.csid),
            'payload': self.payload.decode('utf-8'),
            'status': self.status.name,
            'when_pushed': self.when_pushed.isoformat(),
            'when_deleted': self.when_deleted.isoformat() if self.when_deleted is not None else None,
            'when_delivered': self.when_delivered.isoformat() if self.when_delivered is not None else None,
            'when_error': self.when_error.isoformat() if self.when_error is not None else None,
            'num_attempts': self.num_attempts,
            'last_error': self.last_error
        }
        return json.dumps(dictionary)


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
        with sqlite3.connect(self.db_path, detect_types=sqlite3.PARSE_DECLTYPES) as conn:
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
        with sqlite3.connect(self.db_path, detect_types=sqlite3.PARSE_DECLTYPES) as conn:
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
        with sqlite3.connect(self.db_path, detect_types=sqlite3.PARSE_DECLTYPES) as conn:
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
        with sqlite3.connect(self.db_path, detect_types=sqlite3.PARSE_DECLTYPES) as conn:
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
        with sqlite3.connect(self.db_path, detect_types=sqlite3.PARSE_DECLTYPES) as conn:
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

    def cancel(self, csid: ChecksumID) -> None:
        """
        Cancels a message in the queue.  You cannot cancel a message
        that is being processed, has been archived or abandoned.

        :param csid: The ID of the message to cancel.
        :type csid: ChecksumID
        :raises StateException: No message is in the QUEUED status.
        """
        with sqlite3.connect(self.db_path, detect_types=sqlite3.PARSE_DECLTYPES) as conn:
            cursor = conn.cursor()
            cursor.execute('''UPDATE msgq
                            SET status_id=?
                            WHERE when_deleted IS NULL AND csid=? AND status_id=?''',
                           (Status.CANCELLED.value, str(csid), Status.QUEUED.value))
            if cursor.rowcount < 1:
                raise StateException(
                    f'No message with ID [{csid}] found in QUEUED status.')
            else:
                pass

    def abandon(self, csid: ChecksumID, reason: str) -> None:
        """
        Abandons a message in the PROCESSING status.

        :param csid: The ID of the message to abandon.
        :type csid: ChecksumID
        :param reason: The reason for abandoning the message.
        :type reason: str
        :raises StateException: No message is in the QUEUED status.
        """
        with sqlite3.connect(self.db_path, detect_types=sqlite3.PARSE_DECLTYPES) as conn:
            cursor = conn.cursor()
            cursor.execute('''UPDATE msgq
                            SET status_id=?, last_error=?, when_error=datetime(\'now\'), num_attempts=num_attempts+1
                            WHERE when_deleted IS NULL AND csid=? AND status_id=?''',
                           (Status.ABANDONED.value, reason, str(csid), Status.PROCESSING.value))
            if cursor.rowcount < 1:
                raise StateException(
                    f'No message with ID [{csid}] found in PROCESSING status.')
            else:
                pass

    def find_by_status(self, status: List[Status]) -> List[Message]:
        with sqlite3.connect(self.db_path, detect_types=sqlite3.PARSE_DECLTYPES) as conn:
            placeholders = ','.join(['?'] * len(status))
            cursor = conn.cursor()
            cursor.execute(
                f'''SELECT csid, payload, status_id, when_pushed, when_deleted, when_delivered,
                           when_error, num_attempts, last_error
                    FROM msgq, status
                    WHERE when_deleted IS NULL AND status_id=status.id AND status.name IN ({placeholders})''',
                tuple([s.name for s in status]))
            return [Message(ChecksumID(hexdigest=row[0]),
                            row[1],
                            status=Status(row[2]),
                            when_pushed=row[3],
                            when_deleted=row[4],
                            when_delivered=row[5],
                            when_error=row[6],
                            num_attempts=row[7],
                            last_error=row[8]) for row in cursor.fetchall()]

    @staticmethod
    def __update_status(conn: sqlite3.Connection, csid: ChecksumID, status: Status) -> None:
        conn.execute(
            '''UPDATE msgq SET status_id=? WHERE when_deleted IS NULL AND csid=?''', (status.value, str(csid)))
