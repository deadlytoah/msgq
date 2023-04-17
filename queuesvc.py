import asyncio
import os
import sys
from os import environ, makedirs
from typing import List

import pyservice
from msgq import MessageQueue, QueueName
from pyservice import Metadata, Timeout


class QueueService(pyservice.Service):
    """
    A service that provides a persistent message queue.
    """

    def __init__(self, queue_name: QueueName, message_queue: MessageQueue):
        super().__init__()
        self.queue_name = queue_name
        self.message_queue = message_queue

        self.register_command(
            'push',
            self.push,
            Metadata(
                'push',
                'Pushes a message onto the queue.',
                Timeout.DEFAULT,
                'A list containing the message payload.',
                'An empty list.',
                'ERROR_DATABASE_CONSTRAINT: a message with the given payload is already in the queue.'
            ))

    def __push_impl(self, payload: bytes) -> None:
        self.message_queue.push(payload)

    def name(self) -> str:
        """
        Returns the name of the service.
        """
        return f'Queue Service [{self.queue_name}]'

    def description(self) -> str:
        """
        Returns the description of the service.
        """
        return 'Provides a persistent message queue service.'

    def push(self, arguments: List[str]) -> List[str]:
        """
        Pushes a message onto the queue.

        :param args: An array containing the message payload.
        :type args: List[str]
        :return: An empty list.
        :rtype: List[str]
        """
        self.__push_impl(bytes(arguments[0], 'utf-8'))
        return []


async def main(path: str, queue_name: str) -> None:
    name = QueueName.validated(queue_name)
    message_queue = MessageQueue(path, name)

    # Start the service
    queue_service = QueueService(name, message_queue)
    await queue_service.run(port=36369)


if __name__ == '__main__':
    try:
        path = f'{environ["HOME"]}/.local/queuesvc'
        if not os.path.exists(path):
            makedirs(path)
        asyncio.run(main(path, sys.argv[1]))
    except IndexError:
        print('Must provide a queue name.', file=sys.stderr)
        sys.exit(1)
