import os

from typing import Optional
from pytest_mock.plugin import MockerFixture
from unittest.mock import Mock

from data_management.splits import FileInfo, Split
from model_deployment.searcher import SearchTreeManager, SuccessfulSearch, SearchResult
from model_deployment.proof_manager import ProofManager
from model_deployment.model_wrapper import CodeLLamaServer, ModelResult
from model_deployment.node_score import (
    TokenLengthNormalizedScore,
)

from util.util import get_basic_logger

from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.base_file import CoqFile


_logger = get_basic_logger(__name__)


class TestSearchTree:
    __DUMMY_SPLIT = Split.TEST
    __DUMMY_DATA_LOC = "/"
    __NODE_SCORE_TYPE = TokenLengthNormalizedScore
    __TIMEOUT = 600
    __BRANCH = 4
    __EXPANSIONS = 500

    def __get_dummy_file_info(self, file_path: str) -> FileInfo:
        return FileInfo(
            "hi-dog", file_path, os.path.dirname(file_path), os.path.dirname(file_path)
        )

    def __get_wrapper(
        self, mocker: MockerFixture, model_results: list[ModelResult]
    ) -> Mock:
        wrapper = mocker.Mock(spec=CodeLLamaServer)
        wrapper.formatter = mocker.Mock()
        wrapper.get_recs.side_effect = model_results
        return wrapper

    def __get_result(
        self, test_file: str, mocker: MockerFixture, model_results: list[ModelResult]
    ) -> SearchResult:
        dummy_file_info = self.__get_dummy_file_info(test_file)
        WRAPPER = self.__get_wrapper(mocker, model_results)

        with CoqFile(test_file, workspace=dummy_file_info.workspace) as coq_file:
            _logger.debug("Initially valid: ", coq_file.is_valid)
            last: Optional[int] = None
            for i, step in enumerate(coq_file.steps):
                if "Theorem" in step.text or "Lemma" in step.text:
                    last = i
        assert last is not None

        _logger.debug("Creating Proof File")
        with ProofFile(
            test_file, workspace=dummy_file_info.workspace, timeout=60
        ) as proof_file:
            proof_point = last
            _logger.debug("Creating Proof Manager")
            with ProofManager(
                test_file,
                proof_file,
                proof_point,
                WRAPPER.formatter,
                dummy_file_info,
                TestSearchTree.__DUMMY_SPLIT,
                TestSearchTree.__DUMMY_DATA_LOC,
            ) as proof_manager:
                tree_manager = SearchTreeManager(
                    WRAPPER,
                    proof_manager,
                    TestSearchTree.__NODE_SCORE_TYPE,
                    TestSearchTree.__BRANCH,
                    TestSearchTree.__EXPANSIONS,
                    TestSearchTree.__TIMEOUT,
                )

                _logger.debug("Beginning Proof Search")
                return tree_manager.search(print_trees=True)

    def test_search(self, mocker: MockerFixture):
        result = self.__get_result(
            "test-coq-projs/example.v",
            mocker,
            [
                ModelResult(
                    ["\nintros.", "\nreflexivity."],
                    [10, 20],
                    [15, 5],
                ),
                ModelResult(
                    ["\nauto."],
                    [10],
                    [15],
                )
            ],
        )
        assert isinstance(result, SuccessfulSearch)
        assert result.search_tree.root.model_tactic == ""
        tactics = [
            ("\nreflexivity.", False),
            ("\nintros.", False),
            ("\nauto.", True),
        ]
        for i, node in enumerate(result.search_tree.root.children):
            assert node.model_tactic == tactics[i][0]
            assert node.final_tactic == tactics[i][1]

    def test_search_n_tactics(self, mocker: MockerFixture):
        result = self.__get_result(
            "test-coq-projs/example.v",
            mocker,
            [
                ModelResult(
                    ["\nintros. apply H.", "\nreflexivity."],
                    [10, 20],
                    [15, 5],
                ),
                ModelResult(
                    ["\nauto. apply H2."],
                    [10],
                    [15],
                )
            ],
        )

        assert isinstance(result, SuccessfulSearch)
        assert result.search_tree.root.model_tactic == ""
        tactics = [
            ("\nreflexivity.", False),
            ("\nintros. apply H.", False),
            ("\nintros.", False),
            ("\nauto. apply H2.", False),
            ("\nauto.", True),
        ]
        for i, node in enumerate(result.search_tree.root.children):
            assert node.model_tactic == tactics[i][0]
            assert node.final_tactic == tactics[i][1]
