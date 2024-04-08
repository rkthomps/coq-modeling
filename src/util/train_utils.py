from typing import Any, Optional

import time
import sys, os
import shutil
import subprocess

from yaml import load, Loader
from transformers import TrainingArguments


from util.constants import (
    DATA_CONF_NAME,
    PREMISE_DATA_CONF_NAME,
    RERANK_DATA_CONF_NAME,
    REQS_NAME,
    GIT_NAME,
    TRAINING_CONF_NAME,
)


def load_config(path: str) -> dict[str, Any]:
    with open(path, "r") as fin:
        conf = load(fin, Loader=Loader)
    assert type(conf) == dict
    assert all([type(s) == str for s in conf.keys()])
    return conf


def copy_configs(conf_path: str, conf: dict[str, Any]) -> None:
    output_dir = get_required_arg("output_dir", conf)
    data_path = get_required_arg("data_path", conf)
    if os.path.exists(os.path.join(data_path, DATA_CONF_NAME)):
        data_conf_loc = os.path.join(data_path, DATA_CONF_NAME)
        shutil.copy(data_conf_loc, os.path.join(output_dir, DATA_CONF_NAME))
    elif os.path.exists(os.path.join(data_path, PREMISE_DATA_CONF_NAME)):
        data_conf_loc = os.path.join(data_path, PREMISE_DATA_CONF_NAME)
        shutil.copy(data_conf_loc, os.path.join(output_dir, PREMISE_DATA_CONF_NAME))
    else:
        data_conf_loc = os.path.join(data_path, RERANK_DATA_CONF_NAME)
        shutil.copy(data_conf_loc, os.path.join(output_dir, RERANK_DATA_CONF_NAME))

    shutil.copy(conf_path, os.path.join(output_dir, TRAINING_CONF_NAME))
    reqs = subprocess.check_output([sys.executable, "-m", "pip", "freeze"])
    with open(os.path.join(output_dir, REQS_NAME), "wb") as fout:
        fout.write(reqs)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"])
    with open(os.path.join(output_dir, GIT_NAME), "wb") as fout:
        fout.write(commit)


def make_output_dir(conf: dict[str, Any]) -> None:
    output_dir = get_required_arg("output_dir", conf)
    if os.path.exists(output_dir):
        time_since_created = time.time() - os.path.getctime(output_dir)
        three_mins = 180
        if three_mins < time_since_created:
            print(f"{output_dir} already exists.")
            exit(1)
    else:
        os.makedirs(output_dir)


def get_required_arg(key: str, conf: dict[str, Any]) -> Any:
    if key not in conf:
        print(f"{key} is a required field in the configuration file.")
        exit(1)
    return conf[key]


def get_optional_arg(key: str, conf: dict[str, Any], default: Any) -> Any:
    if key not in conf:
        print(f"{key} not found in configuration. Defaulting to {default}")
        return default
    return conf[key]


def get_training_args(
    conf: dict[str, Any], local_rank: Optional[int]
) -> TrainingArguments:
    return TrainingArguments(
        output_dir=get_required_arg("output_dir", conf),
        per_device_train_batch_size=get_required_arg(
            "per_device_train_batch_size", conf
        ),
        gradient_accumulation_steps=get_optional_arg(
            "gradient_accumulation_steps", conf, 2
        ),
        # optim="paged_adamw_8bit", # causes problems retraining ?
        learning_rate=get_required_arg("learning_rate", conf),
        logging_steps=get_required_arg("logging_steps", conf),
        num_train_epochs=get_required_arg("num_train_epochs", conf),
        max_steps=get_optional_arg("max_steps", conf, -1),
        save_strategy="steps",
        save_steps=get_required_arg("save_steps", conf),
        save_total_limit=get_required_arg("save_total_limit", conf),
        evaluation_strategy="steps",
        eval_steps=get_required_arg("eval_steps", conf),
        per_device_eval_batch_size=get_required_arg("per_device_eval_batch_size", conf),
        eval_accumulation_steps=get_optional_arg("eval_accumulation_steps", conf, 1),
        load_best_model_at_end=True,
        weight_decay=get_optional_arg("weight_decay", conf, 0.0),
        # deepspeed=__get_required_arg("deepspeed", conf),
        local_rank=(local_rank if local_rank else -1),
        ddp_find_unused_parameters=False,
    )
