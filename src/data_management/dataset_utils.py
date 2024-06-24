from __future__ import annotations
from typing import Any


from pathlib import Path
from dataclasses import dataclass

from tactic_gen.lm_example import FormatterConf, formatter_conf_from_yaml
from premise_selection.premise_filter import PremiseFilter, PremiseFilterConf
from premise_selection.rerank_formatter import (
    RerankFormatter,
    RerankFormatterConf,
    rerank_conf_from_yaml,
)


@dataclass
class LmDatasetConf:
    ALIAS = "tactic"
    data_split_loc: Path
    sentence_db_loc: Path
    output_dataset_loc: Path
    lm_formatter_confs: list[FormatterConf]

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> LmDatasetConf:
        assert 0 < len(yaml_data["lm_formatters"])
        return cls(
            Path(yaml_data["data_split_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["output_dataset_loc"]),
            [formatter_conf_from_yaml(f) for f in yaml_data["lm_formatters"]],
        )


@dataclass
class SelectDatasetConf:
    ALIAS = "select"
    data_split_loc: Path
    data_loc: Path
    sentence_db_loc: Path
    output_dataset_loc: Path
    num_negatives_per_positive: int
    num_in_file_negatives_per_positive: int
    context_format_type_alias: str
    premise_format_type_alias: str
    premise_filter_conf: PremiseFilterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> SelectDatasetConf:
        return cls(
            Path(yaml_data["data_split_loc"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["output_dataset_loc"]),
            yaml_data["num_negatives_per_positive"],
            yaml_data["num_in_file_negatives_per_positive"],
            yaml_data["context_format_type_alias"],
            yaml_data["premise_format_type_alias"],
            PremiseFilterConf.from_yaml(yaml_data["premise_filter"]),
        )


@dataclass
class RerankDatasetConf:
    ALIAS = "rerank"
    data_split_loc: Path
    sentence_db_loc: Path
    output_dataset_loc: Path
    rerank_formatter_conf: RerankFormatterConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> RerankDatasetConf:
        return cls(
            Path(yaml_data["data_split_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["output_dataset_loc"]),
            rerank_conf_from_yaml(yaml_data["rerank_formatter"]),
        )



DatasetConf = LmDatasetConf | SelectDatasetConf | RerankDatasetConf

def data_conf_from_yaml(yaml_data: Any) -> DatasetConf:
    attempted_alias = yaml_data["alias"]
    match attempted_alias:
        case LmDatasetConf.ALIAS:
            return LmDatasetConf.from_yaml(yaml_data)
        case SelectDatasetConf.ALIAS:
            return SelectDatasetConf.from_yaml(yaml_data)
        case RerankDatasetConf.ALIAS:
            return RerankDatasetConf.from_yaml(yaml_data)
        case _:
            raise ValueError(f"Dataset type {attempted_alias} unknown.")
