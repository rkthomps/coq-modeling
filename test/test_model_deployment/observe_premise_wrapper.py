from pathlib import Path
from data_management.dataset_file import Sentence
from data_management.splits import DataSplit, Split
from data_management.sentence_db import SentenceDB
from model_deployment.premise_client import (
    TFIdfClient,
    premise_conf_from_yaml,
    premise_client_from_conf,
)


client_conf = {
    "alias": "tfidf",
    "context_format_alias": "basic",
    "premise_format_alias": "basic",
    "premise_filter": {
        "coq_excludes": [
            "THEOREM",
            "LEMMA",
            "DEFINITION",
            "NOTATION",
            "INDUCTIVE",
            "COINDUCTIVE",
            "RECORD",
            "CLASS",
            "INSTANCE",
            "FIXPOINT",
            "COFIXPOINT",
            "SCHEME",
            "VARIANT",
            "FACT",
            "REMARK",
            "COROLLARY",
            "PROPOSITION",
            "PROPERTY",
            "OBLIGATION",
            "TACTIC",
            "RELATION",
            "SETOID",
            "FUNCTION",
            "DERIVE",
            "OTHER",
        ],
        "non_coq_excludes": [
            "DEFINITION",
            "NOTATION",
            "INDUCTIVE",
            "COINDUCTIVE",
            "RECORD",
            "CLASS",
            "INSTANCE",
            "FIXPOINT",
            "COFIXPOINT",
            "SCHEME",
            "VARIANT",
            "OBLIGATION",
            "TACTIC",
            "RELATION",
            "SETOID",
            "FUNCTION",
            "DERIVE",
            "OTHER",
        ],
        "general_excludes": [],
    },
}


data_split = DataSplit.load(Path("splits/random-split.json"))
data_loc = Path("raw-data/coq-dataset")
sentence_db_loc = Path("sentences.db")

sentence_db = SentenceDB.load(sentence_db_loc)
premise_client_conf = premise_conf_from_yaml(client_conf)
premise_client = premise_client_from_conf(premise_client_conf)

print_num = 100
num_steps = 0

for file_info in data_split.get_file_list(Split.VAL):
    try:
        file_dp = file_info.get_dp(data_loc, sentence_db)
    except FileNotFoundError:
        continue
    for proof in file_dp.proofs:
        for step in proof.steps:
            pos_avail_premises = (
                premise_client.premise_filter.get_pos_and_avail_premises(
                    step, proof, file_dp
                )
            )
            prem_gen = premise_client.get_ranked_premise_generator(
                step, proof, pos_avail_premises.avail_premises
            )
            generated: list[Sentence] = []
            for i, prem in enumerate(prem_gen):
                if 100 <= i:
                    break
                generated.insert(0, prem)

            if len(generated) < 100:
                continue

            if len(pos_avail_premises.pos_premises) == 0:
                continue

            if num_steps == print_num:
                print("\n".join([p.text for p in generated]))
                print(premise_client.context_format.format(step, proof))
                print([p.text for p in pos_avail_premises.pos_premises])
                print("Usage: ", step.step.text)
                exit()
            else:
                num_steps += 1
