import os
import sys
from os import environ, makedirs

import pyservice
from TaskQueue import QueueName, TaskQueue


def main(path: str, queue_name: str) -> None:
    name = QueueName.validated(queue_name)
    task_queue = TaskQueue(path, name)

    # Start the service
    pyservice.service_main()


if __name__ == '__main__':
    try:
        path = f'{environ["HOME"]}/.local/queuesvc'
        if not os.path.exists(path):
            makedirs(path)
        main(path, sys.argv[1])
    except IndexError:
        print('Must provide a queue name.', file=sys.stderr)
        sys.exit(1)
