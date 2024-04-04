from __future__ import annotations
from typing import Optional, Any
from dataclasses import dataclass


@dataclass
class PremiseFilterConf:
    coq_excludes: list[str]
    non_coq_excludes: list[str]
    general_excludes: list[str]

    @classmethod
    def from_json(cls, json_data: Any) -> PremiseFilterConf:
        return cls(
            json_data["coq_excludes"],
            json_data["non_coq_excludes"],
            json_data["general_excludes"],
        )


@dataclass
class SelectConf:
    checkpoint_loc: str
    vector_db_loc: Optional[str]

    def to_select_client(self, urls: list[str]) -> SelectClientConf:
        pass

    @classmethod
    def from_json(cls, json_data: Any) -> SelectConf:
        return cls(json_data["checkpoint_loc"], json_data["vector_db_loc"])


@dataclass
class TFIdfConf:
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf

    @classmethod
    def from_json(cls, json_data: Any) -> TFIdfConf:
        return cls(
            json_data["context_format_alias"],
            json_data["premise_format_alias"],
            PremiseFilterConf.from_json(json_data["premise_filter"]),
        )


@dataclass
class BM250OkapiConf:
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf

    @classmethod
    def from_json(cls, json_data: Any) -> BM250OkapiConf:
        return cls(
            json_data["context_format_alias"],
            json_data["premise_format_alias"],
            PremiseFilterConf.from_json(json_data["premise_filter"]),
        )


@dataclass
class SelectClientConf:
    urls: list[str]
    context_format_alias: str
    premise_format_alias: str
    premise_filter_conf: PremiseFilterConf
    sentence_db_loc: str


ClientConf = SelectClientConf | TFIdfConf | BM250OkapiConf
PremiseConf = SelectConf | SelectClientConf | TFIdfConf | BM250OkapiConf
JsonConf = SelectConf | TFIdfConf | BM250OkapiConf


def conf_from_json(conf_data: Any) -> JsonConf:
    match conf_data["alias"]:
        case "select":
            return SelectConf.from_json(conf_data)
        case "tfidf":
            return TFIdfConf.from_json(conf_data)
        case "bm25":
            return BM250OkapiConf.from_json(conf_data)
        case _:
            raise ValueError("Unknown Configuration")
