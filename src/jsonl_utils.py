
from typing import Any, Iterable

import math
import jsonlines
import json
import random
import os

def count_lines(jsonl_file: str) -> int:
    num_lines = 0
    with open(jsonl_file, "r") as fin:
        for _ in fin:
            num_lines += 1
    return num_lines


class SortedBuffer:
    def __init__(self) -> None:
        self.sorted_list: list[tuple[int, Any]] = []

    def insert(self, insert_key: int, insert_value: Any) -> None:
        insert_idx = 0
        while insert_idx < len(self.sorted_list):
            cur_key, cur_values = self.sorted_list[insert_idx]
            if insert_key > cur_key:
                break
            insert_idx += 1
        self.sorted_list.insert(insert_idx, (insert_key, insert_value))

    def get_objects(self) -> Iterable[Any]:
        for _, v in self.sorted_list:
            yield v

    def size(self) -> int:
        return len(self.sorted_list)


def __write_range(in_file: str, 
                out_file: str, 
                start_num:int, 
                end_num:int, 
                mapping: list[int]) -> None:
    buffer = SortedBuffer() 
    with jsonlines.open(in_file, "r") as fin:
        for i, obj in enumerate(fin):
            shuffled_index = mapping[i]
            if start_num <= shuffled_index and shuffled_index < end_num:
                buffer.insert(shuffled_index, obj)
    assert buffer.size() == (end_num - start_num)

    with jsonlines.open(out_file, "a") as fout:
        for obj in buffer.get_objects():
            fout.write(obj)


def shuffle(in_file: str, out_file:str, buffer_size:int = 1000) -> None:
    assert not (in_file == out_file)
    assert not os.path.exists(out_file)
    input_num_lines = count_lines(in_file)
    assignment = list(range(input_num_lines))
    random.shuffle(assignment)
    num_passes = math.ceil(input_num_lines / buffer_size)
    for pass_num in range(num_passes):
        start_idx = pass_num * buffer_size
        end_idx = min(start_idx + buffer_size, input_num_lines) 
        __write_range(in_file, out_file, start_idx, end_idx, assignment)


def split(in_file: str, out_files_and_freqs: dict[str, float]) -> None:
    sum_freqs = sum([freq for _, freq in out_files_and_freqs.items()])
    assert sum_freqs == 1 
    for file, _ in out_files_and_freqs.items():
        assert file != in_file

    writers: list[jsonlines.Writer] = []
    weights: list[float] = []
    for filename, freq in out_files_and_freqs.items():
        writers.append(jsonlines.open(filename, "a"))
        weights.append(freq)

    with jsonlines.open(in_file, "r") as fin:
        for obj in fin:
            selected_writers = random.choices(writers, weights)
            assert len(selected_writers) == 1
            writer = selected_writers[0]
            writer.write(obj)

    for writer in writers:
        writer.close()


def merge(files: list[str], out_file: str) -> None:
    unique_files = set(files)
    assert out_file not in unique_files
    with jsonlines.open(out_file, "w") as fout: 
        for in_file in unique_files:
            with jsonlines.open(in_file, "r") as fin:
                for obj in fin:
                    fout.write(obj)


def get_obj_frequencies(in_file: str) -> dict[str, int]:
    frequencies: dict[str, int] = {}
    with jsonlines.open(in_file, "r") as fin:
        for obj in fin:
            obj_str = json.dumps(obj)
            if obj_str not in frequencies:
                frequencies[obj_str] = 0
            frequencies[obj_str] = frequencies[obj_str] + 1
    return frequencies

def multiset_eq(file1: str, file2: str) -> bool:
    return get_obj_frequencies(file1) == get_obj_frequencies(file2)


def test_shuffle(test_file: str) -> None:
    shuffled_file_loc = test_file + "_shuffled"
    num_lines = count_lines(test_file)
    test_buffer_sizes = [1, num_lines // 3, num_lines // 2 + 5, num_lines, num_lines + 10]
    for buff_size in test_buffer_sizes:
        shuffle(test_file, shuffled_file_loc)
        assert multiset_eq(test_file, shuffled_file_loc) 
        os.remove(shuffled_file_loc)


def get_random_weights(sum_weights: float, num_samples: int) -> list[float]:
    assert num_samples >= 1
    if num_samples == 1:
        return [1 - sum_weights]
    sampled_weight = random.uniform(0, 1 - sum_weights)
    return [sampled_weight] + get_random_weights(sum_weights + sampled_weight, num_samples - 1)


def test_split(test_file: str) -> None:
    for num_splits in range(1, 11):
        weights = get_random_weights(0, num_splits)
        files = [test_file + f"_{n}" for n in range(num_splits)]
        split(test_file, dict(zip(files, weights)))
        merge_file = test_file + f"_merged"
        merge(files, merge_file)
        assert multiset_eq(test_file, merge_file)
        for file in files:
            os.remove(file)
        os.remove(merge_file)


if __name__ == "__main__":
    #shuffle("test_examples.jsonl", "examples-shuffled.jsonl", buffer_size=1000)
    examples_loc = "test_examples.jsonl"
    shuffled_loc = "examples-shuffled.jsonl"
    shuffle(examples_loc, shuffled_loc)
    split_freqs = {
        "examples-train.jsonl": 0.8,
        "examples-val.jsonl": 0.1,
        "examples-test.jsonl": 0.1,
    }
    split(shuffled_loc, split_freqs)
    #test_shuffle("test_examples.jsonl") 


