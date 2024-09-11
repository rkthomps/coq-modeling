import argparse
import os
import yaml
import json
import ipdb
from pathlib import Path
from dataclasses import dataclass

from lemma_gen.lemma_example import LemmaExample, LemmaFormatter, LemmaFormatterConf
from lemma_gen.lemma_model_wrapper import LemmaDecoderWrapper
from data_management.dataset_file import DatasetFile
from data_management.dataset_utils import LemmaDatasetConf
from data_management.sentence_db import SentenceDB
from data_management.create_file_data_point import get_data_point

from util.util import set_rango_logger, get_fresh_path
from util.constants import RANGO_LOGGER, LEMMA_DATA_CONF_NAME

import logging

_logger = logging.getLogger(RANGO_LOGGER)


DATA_POINTS_LOC = Path("raw-data/coq-dataset/data_points")
N_SAMPLES = 10


def get_lemma_formatter_conf(checkpoint_loc: Path) -> LemmaFormatterConf:
    data_conf_loc = checkpoint_loc.parent / LEMMA_DATA_CONF_NAME
    with data_conf_loc.open("r") as fin:
        yaml_conf = yaml.safe_load(fin)
    dataset_conf = LemmaDatasetConf.from_yaml(yaml_conf)
    return dataset_conf.lemma_formatter_conf


@dataclass
class GeneratedExample:
    input_ex: LemmaExample
    generated_outputs: list[str]

    def to_json(self) -> dict:
        return {
            "input_ex": self.input_ex.to_json(),
            "generated_outputs": self.generated_outputs,
        }

    @classmethod
    def from_json(cls, json_data: dict) -> "GeneratedExample":
        return cls(
            LemmaExample.from_json(json_data["input_ex"]),
            json_data["generated_outputs"],
        )


def update_out_file(out_file: Path, examples: list[GeneratedExample]):
    with out_file.open("w") as fout:
        json.dump([ex.to_json() for ex in examples], fout, indent=2)


def read_out_file(out_file: Path) -> list[GeneratedExample]:
    with out_file.open("r") as fin:
        json_data = json.load(fin)
        return [GeneratedExample.from_json(ex) for ex in json_data]


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint_loc", help="Location of model checkpoint.")
    parser.add_argument("file_loc", help="Location of Coq File.")
    parser.add_argument("workspace_loc", help="Location of workspace.")
    parser.add_argument("save_loc", help="Location to save generated lemmas.")

    args = parser.parse_args()

    set_rango_logger(__file__, logging.DEBUG)

    checkpoint_loc = Path(args.checkpoint_loc)
    file_loc = Path(args.file_loc)
    workspace_loc = Path(args.workspace_loc)

    _logger.info(f"Loading model from {checkpoint_loc}")
    model = LemmaDecoderWrapper.from_checkpoint(checkpoint_loc)

    _logger.info("Getting lemma formatter.")
    lemma_formatter_conf = get_lemma_formatter_conf(checkpoint_loc)
    lemma_formatter = LemmaFormatter.from_conf(lemma_formatter_conf)
    _logger.warning("Have not implemented server for lemma generation.")

    sentence_db_loc = get_fresh_path(Path("/tmp"), "sentence_db")
    sentence_db = SentenceDB.create(sentence_db_loc)
    try:
        _logger.info("Getting data point.")
        dp = get_data_point(file_loc, workspace_loc, sentence_db, False, None)

        generated_examples: list[GeneratedExample] = []
        for i, proof in enumerate(dp.proofs):
            _logger.info(f"Generating lemmas for proof {i} / {len(dp.proofs)}.")
            for j, step in enumerate(proof.steps):
                examples = lemma_formatter.examples_from_step(j, proof, dp)
                for example in examples:
                    lemmas = model.get_lemmas(example, N_SAMPLES)
                    generated_examples.append(GeneratedExample(example, lemmas))
                    print("==============================")
                    if example.relevant_lemmas is not None:
                        print("------ Lemmas in Context -----")
                        print("\n".join(example.relevant_lemmas))
                    print("------ State -------")
                    print(example.current_state)
                    print("------ Script -------")
                    print(example.current_script)
                    print("------ Generated Lemmas ------")
                    print("\n".join(lemmas))
                    print("------ Target ------")
                    print(example.target)
                    print("==============================\n")
            update_out_file(Path(args.save_loc), generated_examples)

    finally:
        sentence_db.close()
        os.remove(sentence_db_loc)
