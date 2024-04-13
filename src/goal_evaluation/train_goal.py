
import sys, os
import argparse
from typing import Any, Optional
from pathlib import Path
import transformers
from transformers import Trainer, GPT2Tokenizer, OPTForCausalLM 
from data_management.splits import Split, split_file_path


from goal_evaluation.goal_data import GoalDataset
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
    tokenizer: GPT2Tokenizer,
) -> tuple[GoalDataset, GoalDataset]:
    max_seq_len = get_required_arg("max_seq_len", conf)
    data_path = Path(get_required_arg("data_path", conf))
    num_eval_examples = get_optional_arg("num_eval_examples", conf, None)

    train_path = split_file_path(data_path, Split.TRAIN)
    train_dataset = GoalDataset(
        train_path,
        tokenizer,
        max_seq_len,
    )
    val_path = split_file_path(data_path, Split.VAL)
    val_dataset = GoalDataset(
        val_path,
        tokenizer,
        max_seq_len,
        num_eval_examples,
    )
    return train_dataset, val_dataset


def get_tokenizer(conf: dict[str, Any]) -> GPT2Tokenizer:
    model_name = get_required_arg("model_name", conf)
    tokenizer = GPT2Tokenizer.from_pretrained(model_name, truncation_side="left")
    return tokenizer 


def get_model(conf: dict[str, Any]) -> OPTForCausalLM:
    model_name = get_required_arg("model_name", conf)
    opt = OPTForCausalLM.from_pretrained(model_name)
    return opt

# class (Trainer):
#     def compute_loss(self, model, inputs, return_outputs=False):
#         temp = 0.1
#         cuda_label = inputs["label"].to(model.device)
#         outputs = model(**inputs)
#         similarities = outputs["similarities"]
#         cooled_dots = similarities / temp
#         pos_mask = -1e9 * (1 - cuda_label)
#         pos_weight = torch.logsumexp(cooled_dots + pos_mask, dim=1)
#         total_weight = torch.logsumexp(cooled_dots, dim=1)
#         diffs = pos_weight - total_weight
#         assert (diffs <= 0).all()
#         num_posities = cuda_label.sum(axis=1)
#         pos_avg = diffs / num_posities
#         batch_avg = pos_avg.mean()
#         loss = -1 * batch_avg
#         if return_outputs:
#             return loss, outputs
#         return loss



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
