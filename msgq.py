import hashlib
import sqlite3
from datetime import datetime
from enum import Enum
from typing import Any, Callable, Dict, Optional


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
    Represents a checksum ID.

    :param payload: The message payload.
    :type payload: bytes
    """

    def __init__(self, payload: bytes):
        sha256 = hashlib.sha256(b"", usedforsecurity=False)
        sha256.update(payload)
        self.sha256_digest = sha256.hexdigest()

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
        """
        with sqlite3.connect(self.db_path) as conn:
            when_pushed = datetime.now()
            csid = ChecksumID(payload)
            cursor = conn.cursor()
            cursor.execute(
                '''INSERT INTO msgq (csid, payload, status_id, when_pushed)
                          VALUES (?, ?, ?, ?)''',
                (str(csid), payload, Status.QUEUED.value, when_pushed))

    def get_queued_task(self) -> Optional[Dict[str, Any]]:
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute(
                '''SELECT * FROM tasks WHERE status=? ORDER BY id ASC LIMIT 1''', ('queued',))
            task = cursor.fetchone()
            if task is not None:
                task_dict = {
                    'id': task[0],
                    'function': task[1],
                    'args': eval(task[2]),
                    'kwargs': eval(task[3]),
                    'status': task[4],
                    'last_run': task[5],
                    'num_retries': task[6],
                    'last_result': task[7]
                }
                return task_dict
            else:
                return None

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
