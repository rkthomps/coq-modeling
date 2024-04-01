
import sys, os
import datetime
from util.util import get_fresh_path, DPStartLog, DPEndLog, DPLoadLog, print_info, parse_logs, get_basic_logger


class TestParseLogs:
    def test_parse_logs(self):
        assert os.path.exists(self.out_file)
        timed_logs = parse_logs(self.out_file)
        logs = [l for _, l in timed_logs]
        times = [t for t, _ in timed_logs]
        assert all([isinstance(t, datetime.datetime) for t in times])
        print(logs)
        assert logs == self.logs


    @classmethod
    def setup_class(cls):
        cls.orig_stderr = sys.stderr        
        cls.out_file = get_fresh_path(".", "test_logs") 
        cls.fout = open(cls.out_file, "w")
        sys.stderr = cls.fout
        os.environ["LOG_LEVEL"] = "DEBUG"
        cls.logger = get_basic_logger(__name__)

        cls.logs = [
            DPStartLog("hi"),
            DPLoadLog("hi"),
            DPEndLog("hi"),
        ]

        # Test logs
        for log in cls.logs:
            print_info(log, cls.logger)
        
        assert os.path.exists(cls.out_file)
        with open(cls.out_file) as fin:
            assert 0 < len(fin.read())

    

    @classmethod
    def teardown_class(cls):
        sys.stderr = cls.orig_stderr
        cls.fout.close()
        if os.path.exists(cls.out_file):
            os.remove(cls.out_file)


