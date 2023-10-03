
from __future__ import annotations
from typing import Any

import sys, os
import pdb
import re
from pytorch_lightning.utilities.types import STEP_OUTPUT, OptimizerLRScheduler
from transformers import (ByT5Tokenizer, T5EncoderModel, 
                          get_cosine_schedule_with_warmup,
                          T5ForConditionalGeneration)
import pytorch_lightning as pl  
import torch
import torch.nn.functional as F
from yaml import load, Loader

from premise_selection.training_types import PremiseBatch
from premise_selection.datamodule import tokenize_strings


class PremiseRetriever(pl.LightningModule):
    def __init__(self,
                 model_name: str,
                 lr: float,
                 warmup_steps: int,
                 max_steps: int,
                 max_seq_len: int):
        super(PremiseRetriever, self).__init__()
        assert type(model_name) == str
        assert type(lr) == float
        assert type(warmup_steps) == int
        assert type(max_steps) == int
        assert type(max_seq_len) == int
        self.model_name = model_name
        self.lr = lr
        self.warmup_steps = warmup_steps
        self.max_steps = max_steps
        self.max_seq_len = max_seq_len

        self.tokenizer = ByT5Tokenizer.from_pretrained(model_name)
        self.encoder = T5EncoderModel.from_pretrained(model_name)
        


    def _encode(self, input_ids: torch.Tensor, mask: torch.Tensor) -> torch.Tensor:
        ## TODO: COULD ADD SOME SORT OF "CPU CHECKPOINTING"
        cuda_input_ids = input_ids.to(self.device)
        cuda_mask = mask.to(self.device)
        hidden_states = self.encoder(
            input_ids=cuda_input_ids,
            attention_mask=cuda_mask,
            return_dict=True,
        ).last_hidden_state
        per_batch_counts = cuda_mask.sum(axis=1) 
        masked_hidden_states = hidden_states * cuda_mask[:, :, None]
        summed_hidden_states = masked_hidden_states.sum(axis=1)
        averaged_states = summed_hidden_states / per_batch_counts[:, None]
        return averaged_states 

    def forward(self,
                context_ids: torch.Tensor,
                context_mask: torch.Tensor,
                premise_ids: torch.Tensor,
                premise_mask: torch.Tensor,
                label: torch.Tensor,
                ) -> torch.Tensor: 
        # Loss comes from eq. 2 here: https://proceedings.neurips.cc/paper_files/paper/2020/file/d89a66c7c80a29b1bdbab0f2a1a94af8-Paper.pdf
        context_embs = self._encode(context_ids, context_mask)
        premise_embs = self._encode(premise_ids, premise_mask)
        batch_size = context_ids.shape[0]
        temp = 1
        dots = torch.mm(context_embs, premise_embs.t())
        cooled_dots = dots / temp
        dot_probs = cooled_dots - torch.logsumexp(cooled_dots, dim=1)[:, None]
        cuda_label = label.to(self.device)
        num_posities = cuda_label.sum(axis=1) 
        pos_sum = (dot_probs * cuda_label).sum(axis=1)
        pos_avg = pos_sum / num_posities
        batch_avg = pos_avg.sum() / batch_size 
        loss = -1 * batch_avg 
        return loss

    
    def encode_str(self, to_encode: str) -> torch.Tensor:
        with torch.no_grad():
            tokens = tokenize_strings(
                self.tokenizer, [to_encode], self.max_seq_len) 
            input_ids = tokens.input_ids 
            input_masks = tokens.attention_mask
            encoding = self._encode(input_ids, input_masks) # shape should be 1 x h_dim
            assert encoding.shape[0] == 1
            return encoding 

    
    def training_step(self, premise_batch: PremiseBatch) -> STEP_OUTPUT:
        loss = self.forward(
            premise_batch.context_ids,
            premise_batch.context_mask,
            premise_batch.prem_ids,
            premise_batch.prem_mask,
            premise_batch.label,
        )
        batch_size = premise_batch.context_ids.shape[0]
        self.log("loss", loss, batch_size=batch_size)
        return loss

    
    def validation_step(self, premise_batch: PremiseBatch, batch_idx: int) -> STEP_OUTPUT:
        loss = self.forward(
            premise_batch.context_ids,
            premise_batch.context_mask,
            premise_batch.prem_ids,
            premise_batch.prem_mask,
            premise_batch.label,
        )
        batch_size = premise_batch.context_ids.shape[0]
        self.log("eval_loss", loss, batch_size=batch_size)
        return loss

    
    def configure_optimizers(self) -> OptimizerLRScheduler:
        # TODO: LeanDojo doesn't only use Adam
        optimizer = torch.optim.Adam(self.parameters(), lr=self.lr)
        scheduler = get_cosine_schedule_with_warmup(
            optimizer, self.warmup_steps, self.max_steps) 
        return {
            "optimizer": optimizer, 
            "lr_scheduler": {
                "scheduler": scheduler, 
                "interval": "step"
            }
        } 

    @staticmethod
    def get_model_loc(checkpoint_loc: str) -> str:
        checkpoint_basename = os.path.basename(checkpoint_loc)
        path_suffix = os.path.join(
            "lightning_logs", "version_0", "checkpoints", checkpoint_basename)
        path_disection = re.match(r"(.*?)[\/]" + re.escape(path_suffix), checkpoint_loc)
        if path_disection is None:
            print(f"Checkpoint path doesn't have expected suffix: {path_suffix}")
        model_loc, = path_disection.groups()
        return model_loc
    

    @classmethod
    def get_model_config(cls, checkpoint_loc: str) -> Any:
        model_loc = cls.get_model_loc(checkpoint_loc) 
        model_config_loc = os.path.join(model_loc, "config.yaml")
        with open(model_config_loc, "r") as fin:
            conf = load(fin, Loader=Loader)
        return conf
        

    @classmethod
    def load_from_checkpoint_loc(cls, checkpoint_loc: str) -> PremiseRetriever:
        conf = cls.get_model_config(checkpoint_loc)
        model_args = conf["model"]
        model_args["max_steps"] = conf["trainer"]["max_steps"]
        model_args["max_seq_len"] = conf["data"]["max_seq_len"]
        return cls.load_from_checkpoint(checkpoint_loc, **model_args)


    