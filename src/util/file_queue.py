import os
import shutil
import ast
import time
import pickle
from typing import TypeVar, Optional
from pathlib import Path

T = TypeVar("T")

class EmptyFileQueueError(Exception):
    pass

class QueueNotInitializedError(Exception):
    pass

class FileQueue[T]:
    def __init__(self, queue_loc: Path, sleep_time: float=0.01):
        self.queue_loc = queue_loc
        self.sleep_time = sleep_time
    
    def initialize(self):
        with self.queue_loc.open("w") as _:
            pass
    
    @property
    def lock_loc(self) -> Path:
        return Path(str(self.queue_loc) + ".lock")

    def __check_initialized(self):
        if not self.queue_loc.exists():
            raise QueueNotInitializedError()
    
    def __has_lock(self) -> bool:
        return os.path.exists(self.lock_loc / str(os.getpid()))
        
    def __get_lock(self):
        if self.__has_lock():
            return 
        while True:
            try:
                os.makedirs(self.lock_loc)
                with open(self.lock_loc / str(os.getpid()), "w") as _:
                    pass
                break
            except FileExistsError:
                time.sleep(self.sleep_time)
        assert self.__has_lock()
    
    def __make_line(self, item_bytes: bytes) -> str:
        return f"{item_bytes}\n"
        
    def __release_lock(self):
        assert self.__has_lock()
        shutil.rmtree(self.lock_loc)
        assert not self.__has_lock()

    def put_items(self, items: list[T]):
        self.__check_initialized()
        pass

    def put_all(self, items: list[T]):
        self.__check_initialized()
        self.__get_lock()
        try:
            item_bytestrings = [pickle.dumps(it) for it in items]
            with self.queue_loc.open("a") as fout:
                for ibs in item_bytestrings:
                    fout.write(self.__make_line(ibs))
        finally:
            self.__release_lock()
    
    def put(self, item: T):
        self.__check_initialized()
        self.__get_lock()
        try:
            item_bytestring = pickle.dumps(item)
            with open(self.queue_loc, "a") as fout:
                fout.write(self.__make_line(item_bytestring))
        finally:
            self.__release_lock()
    
    def is_empty(self) -> bool:
        self.__check_initialized()
        self.__get_lock()
        try:
            with self.queue_loc.open("r") as fin:
                for _ in fin:
                    return False
            return True
        finally:
            self.__release_lock()

    def peek(self) -> T:
        self.__check_initialized()
        self.__get_lock()
        try:
            first: Optional[str] = None
            with open(self.queue_loc, "r") as fin:
                for line in fin:
                    first = line
                    break
            if first is None:
                raise EmptyFileQueueError()
            first_bytes = ast.literal_eval(first)
            first_obj = pickle.loads(first_bytes)
            return first_obj
        finally:
            self.__release_lock()


    def get(self) -> T:
        self.__check_initialized()
        self.__get_lock()
        try:
            first: Optional[str] = None
            rest: Optional[str] = None
            with open(self.queue_loc, "r") as fin:
                for line in fin:
                    if first is None:
                        first = line
                    elif rest is None:
                        rest = line
                    else:
                        rest += line
            if first is None:
                raise EmptyFileQueueError()
            if rest is None:
                with open(self.queue_loc, "w") as fout:
                    pass
            else:
                with open(self.queue_loc, "w") as fout:
                    fout.write(rest)
            first_bytes = ast.literal_eval(first)
            first_obj = pickle.loads(first_bytes)
            return first_obj
        finally:
            self.__release_lock()


                    

