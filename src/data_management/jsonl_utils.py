from typing import Any, Iterable, Optional

import edist
import math
import jsonlines
import json
import random
import os
import shutil
from tqdm import tqdm


def count_lines(jsonl_file: str) -> int:
    num_lines = 0
    with open(jsonl_file, "r") as fin:
        for _ in fin:
            num_lines += 1
    return num_lines


def __write_range(
    in_file: str, out_file: str, start_num: int, end_num: int, mapping: list[int]
) -> None:
    # buffer = SortedBuffer()
    buffer_size = end_num - start_num
    buffer: list[Optional[str]] = [None] * buffer_size
    with open(in_file, "r") as fin:
        for i, line in enumerate(fin):
            shuffled_index = mapping[i]
            if start_num <= shuffled_index < end_num:
                buffer_index = shuffled_index - start_num
                buffer[buffer_index] = line

    with open(out_file, "a") as fout:
        for out_str in buffer:
            match out_str:
                case None:
                    raise ValueError("Expected str to write")
                case _:
                    fout.write(out_str)


def shuffle(in_file: str, out_file: str, buffer_size: int = 100000) -> None:
    assert not (in_file == out_file)
    assert not os.path.exists(out_file)
    if buffer_size < 1:
        raise ValueError("Buffer size cannot be less than one.")
    input_num_lines = count_lines(in_file)
    if input_num_lines <= 0:
        shutil.copy(in_file, out_file)
        return
    # Can quickly go from input -> assignment
    # But I want to be able to go from assignment -> input
    assignment = list(range(input_num_lines))
    random.shuffle(assignment)
    num_passes = math.ceil(input_num_lines / buffer_size)
    for pass_num in tqdm(range(num_passes)):
        start_idx = pass_num * buffer_size
        end_idx = min(start_idx + buffer_size, input_num_lines)
        __write_range(in_file, out_file, start_idx, end_idx, assignment)


def __load_cmp_chunk(in_file: str, start: int, end: int) -> tuple[set[str], int]:
    chunk_set: set[str] = set()
    num_duplicates = 0
    with open(in_file, "r") as fin:
        for i, line in enumerate(fin):
            if i >= end:
                return chunk_set, num_duplicates
            if i < start:
                continue
            if line in chunk_set:
                num_duplicates += 1
            chunk_set.add(line)
    return chunk_set, num_duplicates


def __vet_chunk(chunk: set[str], in_file: str, vet_start: int) -> int:
    chunk_num_duplicates = 0
    with open(in_file, "r") as fin:
        for i, line in enumerate(fin):
            if i < vet_start:
                continue
            try:
                chunk.remove(line)
                chunk_num_duplicates += 1
            except KeyError:
                continue
    return chunk_num_duplicates


def __write_chunk(chunk: set[str], out_file: str) -> None:
    with open(out_file, "a") as fout:
        for line in chunk:
            fout.write(line)


def deduplicate(in_file: str, out_file: str, buffer_size: int = 100000) -> int:
    assert not (in_file == out_file)
    assert not os.path.exists(out_file)
    if buffer_size < 1:
        raise ValueError("Buffer size cannot be less than one.")
    input_num_lines = count_lines(in_file)
    if input_num_lines <= 0:
        shutil.copy(in_file, out_file)
        return 0
    num_passes = math.ceil(input_num_lines / buffer_size)
    num_duplicates = 0
    for i in tqdm(range(num_passes)):
        chunk_start = i * buffer_size
        chunk_end = min(chunk_start + buffer_size, input_num_lines)
        chunk_set, init_num_dups = __load_cmp_chunk(in_file, chunk_start, chunk_end)
        if chunk_end < input_num_lines:
            vet_num_dups = __vet_chunk(chunk_set, in_file, chunk_end)
        else:
            vet_num_dups = 0
        num_duplicates += init_num_dups + vet_num_dups
        __write_chunk(chunk_set, out_file)
    return num_duplicates
