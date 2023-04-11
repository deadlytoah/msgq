import sqlite3
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
        for character in queue_name:
            if character not in QueueName.VALID_CHARACTERS:
                raise ValueError(
                    f'Invalid queue name: {queue_name}. Must consist of characters in [{QueueName.VALID_CHARACTERS}]')
            else:
                pass
        return QueueName(queue_name)


class TaskQueue:
    def __init__(self, path: str, name: QueueName):
        self.db_path = f'{path}/{name}.db'
        with sqlite3.connect(self.db_path) as conn:
            conn.execute('''CREATE TABLE IF NOT EXISTS tasks
                            (id INTEGER PRIMARY KEY AUTOINCREMENT,
                             function TEXT NOT NULL,
                             args TEXT,
                             kwargs TEXT,
                             status TEXT NOT NULL,
                             last_run INTEGER,
                             num_retries INTEGER DEFAULT 0,
                             last_result TEXT)''')

    def add_task(self, func: Callable, args: Optional[tuple] = None,
                 kwargs: Optional[Dict[str, Any]] = None):
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute('''INSERT INTO tasks
                              (function, args, kwargs, status)
                              VALUES (?, ?, ?, ?)''',
                           (func.__name__, str(args), str(kwargs), 'queued'))

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
