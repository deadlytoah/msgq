import asyncio
import os
import sys
from os import environ, makedirs
from typing import List

import pyservice
from msgq import MessageQueue, QueueName


class QueueService(pyservice.Service):
    def __init__(self, queue_name: QueueName, message_queue: MessageQueue):
        super().__init__()
        self.queue_name = queue_name
        self.message_queue = message_queue

    def name(self) -> str:
        return f'queue[{self.queue_name}]'

    def description(self) -> str:
        return 'Provides a persistent message queue service.'

    def enqueue(self, arguments: List[str]) -> None:
        self.message_queue.add_task(*parameters)


async def main(path: str, queue_name: str) -> None:
    name = QueueName.validated(queue_name)
    message_queue = MessageQueue(path, name)

    # Start the service
    queue_service = QueueService(message_queue)
    await queue_service.run()


if __name__ == '__main__':
    try:
        path = f'{environ["HOME"]}/.local/queuesvc'
        if not os.path.exists(path):
            makedirs(path)
        asyncio.run(main(path, sys.argv[1]))
    except IndexError:
        print('Must provide a queue name.', file=sys.stderr)
        sys.exit(1)
