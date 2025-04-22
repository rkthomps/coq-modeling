from typing import Any


from model_deployment.proof_manager import ProofManager
from model_deployment.tactic_gen_client import TacticGenClient
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
from model_deployment.whole_proof_searcher import (
    WholeProofSearcherConf,
    WholeProofSearcher,
    WholeProofSuccess,
    WholeProofFailure,
)
from model_deployment.diversity_searcher import (
    DiversitySearcherConf,
    DiversitySearcher,
)

SuccessfulSearch = ClassicalSuccess | StraightLineSuccess | WholeProofSuccess
FailedSearch = ClassicalFailure | StraightLineFailure | WholeProofFailure
SearchResult = SuccessfulSearch | FailedSearch

Searcher = ClassicalSearcher | StraightLineSearcher | WholeProofSearcher | DiversitySearcher
SearcherConf = ClassicalSearchConf | StraightLineSearcherConf | WholeProofSearcherConf | DiversitySearcherConf


def searcher_conf_from_yaml(yaml_data: Any) -> SearcherConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case ClassicalSearchConf.ALIAS:
            return ClassicalSearchConf.from_yaml(yaml_data)
        case StraightLineSearcherConf.ALIAS:
            return StraightLineSearcherConf.from_yaml(yaml_data)
        case WholeProofSearcherConf.ALIAS:
            return WholeProofSearcherConf.from_yaml(yaml_data)
        case DiversitySearcherConf.ALIAS:
            return DiversitySearcherConf.from_yaml(yaml_data)
        case _:
            raise ValueError("Searcher not found.")


def searcher_from_conf(
    conf: SearcherConf, tactic_gens: list[TacticGenClient], manager: ProofManager
) -> Searcher:
    match conf:
        case ClassicalSearchConf():
            return ClassicalSearcher.from_conf(conf, tactic_gens, manager)
        case StraightLineSearcherConf():
            return StraightLineSearcher.from_conf(conf, tactic_gens, manager)
        case WholeProofSearcherConf():
            return WholeProofSearcher.from_conf(conf, tactic_gens, manager)
        case DiversitySearcherConf():
            return DiversitySearcher.from_conf(conf, tactic_gens, manager)
