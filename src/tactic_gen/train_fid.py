import sys, os
import argparse
from typing import Any, Optional
import transformers
from transformers import Trainer, T5Tokenizer, T5ForConditionalGeneration
from data_management.splits import Split, split_file_path


from tactic_gen.fid_data import FidDataset
from tactic_gen.fid_model import FiDT5
from util.train_utils import (
    get_optional_arg,
    get_required_arg,
    get_training_args,
    load_config,
    make_output_dir,
    copy_configs,
)


def get_datasets(
    conf: dict[str, Any],
    tokenizer: T5Tokenizer,
) -> tuple[FidDataset, FidDataset]:
    max_encode_len = get_required_arg("max_encode_len", conf)
    max_decode_len = get_required_arg("max_decode_len", conf)
    max_num_passages = get_required_arg("max_num_passages", conf)

    data_path = get_required_arg("data_path", conf)
    num_eval_examples = get_optional_arg("num_eval_examples", conf, None)

    train_path = split_file_path(data_path, Split.TRAIN)
    train_dataset = FidDataset(
        train_path, tokenizer, max_encode_len, max_decode_len, max_num_passages
    )
    val_path = split_file_path(data_path, Split.VAL)
    val_dataset = FidDataset(
        val_path,
        tokenizer,
        max_encode_len,
        max_decode_len,
        max_num_passages,
        num_eval_examples,
    )
    return train_dataset, val_dataset


def get_tokenizer(conf: dict[str, Any]) -> T5Tokenizer:
    model_name = get_required_arg("model_name", conf)
    return T5Tokenizer.from_pretrained(model_name)


def get_model(conf: dict[str, Any]) -> T5ForConditionalGeneration:
    model_name = get_required_arg("model_name", conf)
    t5 = T5ForConditionalGeneration.from_pretrained(model_name)
    fid_model = FiDT5(t5.config)
    fid_model.load_t5(t5.state_dict())
    return fid_model


def get_trainer(
    conf: dict[str, Any], local_rank: Optional[int], checkpoint_name: Optional[str]
) -> Trainer:

    print("\n\nBuilding Training Config...")
    training_args = get_training_args(conf, local_rank)
    print("\n\nRetrieving Tokenizer...")
    tokenizer = get_tokenizer(conf)

    print("\n\nRetrieving Model...")
    model = get_model(conf)

    print("\n\nConstructing Dataset...")
    train_dataset, val_dataset = get_datasets(conf, tokenizer)

    print("\n\nBuilding Trainer...")
    return Trainer(
        model=model,
        args=training_args,
        train_dataset=train_dataset,
        eval_dataset=val_dataset,
        data_collator=train_dataset.collate,
        tokenizer=tokenizer,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Train code llama by providing a .yaml config file. As an example, see src/tactic_gen/confs/basic_train.yaml"
    )
    print(f"<ARGV>{sys.argv}</ARGV")
    parser.add_argument(
        "--local_rank",
        type=int,
        default=-1,
        help="local rank passed from distributed launcher",
    )
    parser.add_argument("yaml_config", help="yaml config file to use for training.")
    args = parser.parse_args(sys.argv[1:])
    conf = load_config(args.yaml_config)
    train_from_checkpoint = (
        conf["checkpoint_name"] if "checkpoint_name" in conf else None
    )
    trainer = get_trainer(conf, args.local_rank, train_from_checkpoint)
    if train_from_checkpoint:
        checkpoint_name = conf["checkpoint_name"]
        print(f"Training from checkpoint {checkpoint_name}")
        transformers.logging.set_verbosity_info()
        trainer.train(checkpoint_name)
    else:
        make_output_dir(conf)
        copy_configs(args.yaml_config, conf)
        print("Training from scratch")
        trainer.train()