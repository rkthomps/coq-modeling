from typing import Any


from model_deployment.proof_manager import ProofManager
from model_deployment.tactic_gen_client import TacticGenClient
from model_deployment.mcts_searcher import (
    MCTSConf,
    MCTSSearcher,
    MCTSSuccess,
    MCTSFailure,
)
from model_deployment.classical_searcher import (
    ClassicalSearchConf,
    ClassicalSearcher,
    ClassicalSuccess,
    ClassicalFailure,
)
from model_deployment.straight_line_searcher import (
    StraightLineSearcherConf,
    StraightLineSearcher,
    StraightLineSuccess,
    StraightLineFailure,
)

SuccessfulSearch = ClassicalSuccess | MCTSSuccess | StraightLineSuccess
FailedSearch = ClassicalFailure | MCTSFailure | StraightLineFailure
SearchResult = SuccessfulSearch | FailedSearch

Searcher = ClassicalSearcher | MCTSSearcher | StraightLineSearcher
SearcherConf = ClassicalSearchConf | MCTSConf | StraightLineSearcherConf


def searcher_conf_from_yaml(yaml_data: Any) -> SearcherConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case ClassicalSearchConf.ALIAS:
            return ClassicalSearchConf.from_yaml(yaml_data)
        case MCTSConf.ALIAS:
            return MCTSConf.from_yaml(yaml_data)
        case StraightLineSearcherConf.ALIAS:
            return StraightLineSearcherConf.from_yaml(yaml_data)
        case _:
            raise ValueError("Searcher not found.")


def searcher_from_conf(
    conf: SearcherConf, tactic_gen: TacticGenClient, manager: ProofManager
) -> Searcher:
    match conf:
        case ClassicalSearchConf():
            return ClassicalSearcher.from_conf(conf, tactic_gen, manager)
        case MCTSConf():
            return MCTSSearcher.from_conf(conf, tactic_gen, manager)
        case StraightLineSearcherConf():
            return StraightLineSearcher.from_conf(conf, tactic_gen, manager)
