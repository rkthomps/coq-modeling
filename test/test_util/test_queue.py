import os
from pathlib import Path

import pytest

from util.file_queue import FileQueue, EmptyFileQueueError, QueueNotInitializedError


class TestQueue:
    def test_get_and_put(self):
        queue: FileQueue[str] = FileQueue(self.queue_loc)
        queue.initialize()
        assert queue.is_empty()
        s1 = "hi bob"
        s2 = "hi jimmy"
        queue.put(s1)
        queue.put(s2)
        assert s1 == queue.get()
        assert s2 == queue.get()
        assert queue.is_empty()
        queue.put_all([s1, s2, s1, s2])
        assert s1 == queue.get()
        assert s2 == queue.get()
        assert s1 == queue.peek()
        assert s1 == queue.get()
        assert s2 == queue.get()
        with pytest.raises(EmptyFileQueueError) as _:
            queue.get()

    def test_uninitialized(self):
        queue: FileQueue[int] = FileQueue(Path("test_queue"))
        with pytest.raises(QueueNotInitializedError) as _:
            queue.put(1)
        with pytest.raises(QueueNotInitializedError) as _:
            queue.get()
        with pytest.raises(QueueNotInitializedError) as _:
            queue.peek()
        with pytest.raises(QueueNotInitializedError) as _:
            queue.is_empty()
        with pytest.raises(QueueNotInitializedError) as _:
            queue.put_all([1, 2, 3])

    @classmethod
    def setup_class(cls):
        cls.queue_loc = Path("queue")

    @classmethod
    def teardown_class(cls):
        if cls.queue_loc.exists():
            os.remove(cls.queue_loc)
