import argparse
import asyncio
import os
import sys
from os import environ, makedirs
from typing import List, Optional

import pyservice
from msgq import ChecksumID, MessageQueue, QueueName
from pyservice.metadata import Argument, Arguments, Metadata, Timeout


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
                Arguments(Argument('payload', 'The message payload to push.')),
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
                Arguments.none(),
                '''Returns ID and payload of the next message to process,
                   or an empty list if the queue is empty.''',
                'None',
            ))
        self.register_command(
            'archive',
            self.archive,
            Metadata(
                'archive',
                'Archives the given message in the queue that is in PROCESSING status.',
                Timeout.DEFAULT,
                Arguments(
                    Argument('message ID', 'The ID of the message to archive.')),
                'None',
                'ERROR_MSGQ_STATE: There was no message in PROCESSING status.',
            ))
        self.register_command(
            'fail',
            self.fail,
            Metadata(
                'fail',
                'Fails the given message in the queue that is in PROCESSING status.',
                Timeout.DEFAULT,
                Arguments(
                    Argument('message ID', 'The ID of the message to fail.')),
                'None',
                'ERROR_MSGQ_STATE: There was no message in PROCESSING status.',
            ))
        self.register_command(
            'cancel',
            self.cancel,
            Metadata(
                'cancel',
                'Cancels the given message in the queue that is in QUEUED status.',
                Timeout.DEFAULT,
                Arguments(
                    Argument('message ID', 'The ID of the message to cancel.')),
                'None',
                'ERROR_MSGQ_STATE: There was no message in QUEUED status.',
            ))

    def __push_impl(self, payload: bytes) -> None:
        self.message_queue.push(payload)

    def __process_impl(self) -> Optional[tuple[ChecksumID, bytes]]:
        return self.message_queue.process()

    def __fail_impl(self, csid: ChecksumID, reason: str) -> None:
        self.message_queue.fail(csid, reason)

    def __cancel_impl(self, csid: ChecksumID) -> None:
        self.message_queue.cancel(csid)

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
        Returns ID and payload of the next message to process in the queue,
        or None if the queue is empty.

        :return: A list containing ID and payload of the next message to
                 process, or None if the queue is empty.
        :rtype: List[str]
        """
        result = self.__process_impl()
        if result is not None:
            (csid, payload) = result
            return [str(csid), payload.decode('utf-8')]
        else:
            return []

    def archive(self, arguments: List[str]) -> List[str]:
        """
        Archives the given message in PROCESSING status in the queue.

        :param args: An array containing the message ID.
        :type args: List[str]
        :return: An empty list.
        :rtype: List[str]
        :raises ValueError: The message ID argument is missing.
        :raises MsgQStateException: There was no message in PROCESSING status.
        """
        if len(arguments) == 1:
            csid = ChecksumID(hexdigest=arguments[0])
            self.message_queue.archive(csid)
            return []
        else:
            raise ValueError('Must provide a message ID as the argument.')

    def fail(self, arguments: List[str]) -> List[str]:
        """
        Fails the given message in PROCESSING status in the queue.

        :param args: An array containing the message ID and the reason for
                     the failure.
        :type args: List[str]
        :return: An empty list.
        :rtype: List[str]
        :raises ValueError: The message ID argument is missing.
        :raises MsgQStateException: There was no message in PROCESSING status.
        """
        if len(arguments) == 2:
            csid = ChecksumID(hexdigest=arguments[0])
            reason = arguments[1]
            self.__fail_impl(csid, reason)
            return []
        else:
            raise ValueError('''Must provide a message ID and the reason for
                                the failure as the argument.''')

    def cancel(self, arguments: List[str]) -> List[str]:
        """
        Cancels the given message in QUEUED status in the queue.

        :param args: An array containing the message ID.
        :type args: List[str]
        :return: An empty list.
        :rtype: List[str]
        :raises ValueError: The message ID argument is missing.
        :raises MsgQStateException: There was no message in QUEUED status.
        """
        if len(arguments) == 1:
            csid = ChecksumID(hexdigest=arguments[0])
            self.__cancel_impl(csid)
            return []
        else:
            raise ValueError('Must provide a message ID as the argument.')


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
