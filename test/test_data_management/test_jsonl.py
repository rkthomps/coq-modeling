from typing import Any
import sys, os
import ipdb
import json
import pytest
from hypothesis import given, strategies as st, assume

from data_management.jsonl_utils import shuffle, deduplicate


class TestJsonlUtils:
    @staticmethod
    def __get_obj_frequencies(objs: list[str]) -> dict[str, int]:
        frequencies: dict[str, int] = {}
        for obj in objs:
            if obj not in frequencies:
                frequencies[obj] = 0
            frequencies[obj] += 1
        return frequencies

    @staticmethod
    def __file_lines(in_file: str) -> list[str]:
        lines: list[str] = []
        with open(in_file, "r") as fin:
            for line in fin:
                lines.append(line)
        return lines

    @classmethod
    def __multiset_eq(cls, file1: str, file2: str) -> bool:
        obj1_freqs = cls.__get_obj_frequencies(cls.__file_lines(file1))
        obj2_freqs = cls.__get_obj_frequencies(cls.__file_lines(file2))
        return obj1_freqs == obj2_freqs

    def __write_in_file(self, in_list: list[str]) -> None:
        with open(self.in_file, "w") as fout:
            for line in in_list:
                fout.write(json.dumps(line) + "\n")

    def test_empty(self) -> None:
        self.__write_in_file([""])
        if os.path.exists(self.out_file):
            os.remove(self.out_file)
        shuffle(self.in_file, self.out_file)
        assert self.__multiset_eq(self.in_file, self.out_file)

    @given(st.lists(st.text()), st.integers())
    def test_shuffle_buff_nonzero(self, in_list: list[str], buff_size: int) -> None:
        assume(buff_size > 0)
        assume(len(in_list) > 0)
        self.__write_in_file(in_list)
        if os.path.exists(self.out_file):
            os.remove(self.out_file)
        shuffle(self.in_file, self.out_file, buff_size)
        assert self.__multiset_eq(self.in_file, self.out_file)

    @given(st.lists(st.text()))
    def test_shuffle_buff_zero(self, in_list: list[str]) -> None:
        assume(len(in_list) > 0)
        with pytest.raises(ValueError):
            if os.path.exists(self.out_file):
                os.remove(self.out_file)
            self.__write_in_file(in_list)
            shuffle(self.in_file, self.out_file, buffer_size=0)

    @given(st.integers())
    def test_shuffle_list_zero(self, buff_size: int) -> None:
        assume(buff_size > 0)
        with pytest.raises(AssertionError):
            if os.path.exists(self.out_file):
                os.remove(self.out_file)
            self.__write_in_file([])
            shuffle(self.in_file, self.out_file, buff_size)

    @given(st.lists(st.text()), st.integers())
    def test_deduplicate(self, in_list: list[str], buff_size: int) -> None:
        assume(buff_size > 0)
        assume(len(in_list) > 0)
        if os.path.exists(self.out_file):
            os.remove(self.out_file)
        self.__write_in_file(in_list)
        start_lines = self.__file_lines(self.in_file)
        in_set = list(set(start_lines))
        num_duplicates = deduplicate(self.in_file, self.out_file, buff_size)
        multiset_of_set = self.__get_obj_frequencies(in_set)
        multiset_of_out = self.__get_obj_frequencies(self.__file_lines(self.out_file))
        assert multiset_of_set == multiset_of_out
        assert (len(in_list) - len(in_set)) == num_duplicates

    @given(st.integers())
    def test_empty_deduplicate(self, buff_size: int) -> None:
        assume(buff_size > 0)
        with pytest.raises(AssertionError):
            if os.path.exists(self.out_file):
                os.remove(self.out_file)
            self.__write_in_file([])
            deduplicate(self.in_file, self.out_file, buff_size)

    @given(st.lists(st.integers()))
    def test_deduplicate_zero_buff(self, in_list: list[str]) -> None:
        assume(len(in_list) > 0)
        with pytest.raises(ValueError):
            if os.path.exists(self.out_file):
                os.remove(self.out_file)
            self.__write_in_file(in_list)
            deduplicate(self.in_file, self.out_file, 0)

    @classmethod
    def setup_class(cls) -> None:
        cls.in_file = "in.jsonl"
        cls.out_file = "out.jsonl"

    @classmethod
    def teardown_class(cls) -> None:
        if os.path.exists(cls.in_file):
            os.remove(cls.in_file)
        if os.path.exists(cls.out_file):
            os.remove(cls.out_file)