from typing import Any, Optional

from transformers import TrainingArguments


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
        save_strategy="epoch",
        save_total_limit=get_required_arg("save_total_limit", conf),
        evaluation_strategy="steps",
        eval_steps=get_required_arg("eval_steps", conf),
        per_device_eval_batch_size=get_required_arg("per_device_eval_batch_size", conf),
        eval_accumulation_steps=get_optional_arg("eval_accumulation_steps", conf, 1),
        # deepspeed=__get_required_arg("deepspeed", conf),
        local_rank=(local_rank if local_rank else -1),
        ddp_find_unused_parameters=False,
    )
