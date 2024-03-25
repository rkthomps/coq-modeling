
from typing import Callable 
import os
import time
import random

from data_management.sentence_db import SentenceDB


SENTENCE_DB_LOC = "./sentences.db"

Benchmark = Callable[[SentenceDB], None]

def timeit(fn: Benchmark, sdb: SentenceDB) -> float: 
    start = time.time()
    fn(sdb)
    end = time.time()
    return end - start


def print_benchmark(fn: Benchmark, sdb: SentenceDB, msg: str) -> None:
    print("{:50s}; Time: {:10f}".format(msg, timeit(fn, sdb)))


def get_many_indices(sdb: SentenceDB):
    for i in range(1, 10001):
        sdb.retrieve(i)

def get_many_random_indices(sdb: SentenceDB):
    random.seed(0)
    indices = random.sample(range(1, 100001), 10000)
    for i in indices:
        sdb.retrieve(i)

def find_indices(sdb: SentenceDB):
    sentences = [sdb.retrieve(i) for i in range(1, 10000)]
    for s in sentences:
        sdb.find_sentence(s)

if __name__ == "__main__":
    if not os.path.exists(SENTENCE_DB_LOC):
        raise FileNotFoundError(SENTENCE_DB_LOC)
    sdb = SentenceDB.load(SENTENCE_DB_LOC)
    get_many_random_indices(sdb)
    print_benchmark(get_many_indices, sdb, "Getting 10000 indices: ")
    print_benchmark(get_many_random_indices, sdb, "Getting 10000 random indices out of first 100000: ")
    print_benchmark(find_indices, sdb, "Finding 10000 sentences: ")
   

