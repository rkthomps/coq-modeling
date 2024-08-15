from pathlib import Path
from data_management.sentence_db import SentenceDB
from data_management.dataset_file import DatasetFile
from data_management.create_file_data_point import get_data_point, get_switch_loc
from util.util import get_basic_logger
import ipdb
import pytest

_logger = get_basic_logger(__name__)

DATA_LOC = Path("raw-data/coq-dataset")


class TestCreateFileDataPoint:
    @pytest.mark.skip(reason="Test taking too long.")
    def test_create_file_data_point(self):
        reference_workspace_loc = DATA_LOC / "repos/coq-community-sudoku"
        reference_file_loc = reference_workspace_loc / "theories/ListAux.v"
        referece_data_point_loc = (
            DATA_LOC / "data_points/coq-community-sudoku-theories-ListAux.v"
        )
        sentence_db_loc = DATA_LOC / "sentences.db"
        if not referece_data_point_loc.exists():
            _logger.warning(
                f"File not found: {referece_data_point_loc}. Skipping test."
            )
            return
        if not sentence_db_loc.exists():
            _logger.warning(f"File not found: {sentence_db_loc}. Skipping test.")
            return

        sentence_db = SentenceDB.load(sentence_db_loc)
        referece_dp = DatasetFile.load(referece_data_point_loc, sentence_db)

        new_dp = get_data_point(
            reference_file_loc,
            reference_workspace_loc,
            sentence_db,
            add_to_dataset=True,
            switch_loc=get_switch_loc(),
        )

        assert referece_dp == new_dp


if __name__ == "__main__":
    TestCreateFileDataPoint().test_create_file_data_point()
