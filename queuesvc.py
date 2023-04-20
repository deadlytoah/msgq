import argparse
import asyncio
import os
import sys
from os import environ, makedirs
from typing import List, Optional

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
        self.register_command(
            'process',
            self.process,
            Metadata(
                'process',
                'Returns the next message to process in the queue.',
                Timeout.DEFAULT,
                'None',
                'The payload of the next message to process.',
                'None',
            ))

    def __push_impl(self, payload: bytes) -> None:
        self.message_queue.push(payload)

    def __process_impl(self) -> Optional[bytes]:
        return self.message_queue.process()

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
        :raises DatabaseConstraintException: A message with the given payload
                                             is already in the queue.
        :raises ValueError: The message payload argument is missing.
        """
        if len(arguments) == 1:
            self.__push_impl(bytes(arguments[0], 'utf-8'))
            return []
        else:
            raise ValueError('Must provide a message payload as the argument.')

    def process(self, _arguments: List[str]) -> List[str]:
        """
        Returns the next message to process in the queue, or None if the
        queue is empty.

        :return: The payload of the next message to process, or None if the
                 queue is empty.
        :rtype: List[str]
        """
        payload = self.__process_impl()
        if payload is not None:
            return [payload.decode('utf-8')]
        else:
            return []


async def main(path: str, queue_name: str, port: Optional[int] = None) -> None:
    name = QueueName.validated(queue_name)
    message_queue = MessageQueue(path, name)

    # Start the service
    queue_service = QueueService(name, message_queue)
    await queue_service.run(port=port)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Persistent Queue Service')
    parser.add_argument('queue_name', type=str, help='The name of the queue.')
    parser.add_argument('-p', '--port', type=int,
                        help='The port to listen on.')
    args = parser.parse_args()

    path = f'{environ["HOME"]}/.local/queuesvc'
    if not os.path.exists(path):
        makedirs(path)
    asyncio.run(main(path, args.queue_name, port=args.port))
