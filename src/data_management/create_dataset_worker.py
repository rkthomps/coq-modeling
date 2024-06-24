import sys, os
import argparse
from pathlib import Path

from data_management.dataset_utils import DatasetConf, data_conf_from_yaml

from util.file_queue import FileQueue, EmptyFileQueueError



if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dataset_conf_loc", help="Location of dataset configuration.")
    parser.add_argument("queue_loc", help="Location of the work queue.")
    parser.add_argument("worker_id", type=int, help="Identifier for this worker.")

    args = parser.parse_args(sys.argv[1:])
    dataset_conf_loc = Path(args.dataset_conf_loc)
    queue_loc = Path(args.queue_loc)

    assert dataset_conf_loc.exists()
    assert queue_loc.exists() 

    dataset_conf = data_conf_from_yaml(dataset_conf_loc)


