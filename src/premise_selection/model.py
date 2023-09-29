
from __future__ import annotations
from typing import Any

import sys, os
import pdb
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
        return F.normalize(averaged_states, dim=1) 

    def forward(self,
                context_ids: torch.Tensor,
                context_mask: torch.Tensor,
                premise_ids: torch.Tensor,
                premise_mask: torch.Tensor,
                label: torch.Tensor,
                ) -> torch.Tensor: 
        context_embs = self._encode(context_ids, context_mask)
        premise_embs = self._encode(premise_ids, premise_mask)
        similarity = torch.mm(context_embs, premise_embs.t())
        epsilon = 1e-4
        assert (-1 - epsilon) <= similarity.min() <= similarity.max() <= (1 + epsilon)
        cuda_label = label.to(self.device) 
        loss = F.mse_loss(similarity, cuda_label) 
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


    @classmethod
    def load_from_conf_and_checkpoint(cls, model_loc: str, checkpoint_name: str
                                      ) -> PremiseRetriever:
        config_loc = os.path.join(model_loc, "config.yaml")
        with open(config_loc, "r") as fin:
            conf = load(fin, Loader=Loader) 
        model_args = conf["model"]
        model_args["max_steps"] = conf["trainer"]["max_steps"]
        model_args["max_seq_len"] = conf["data"]["max_seq_len"]
        checkpoint_loc = os.path.join(
            model_loc, "lightning_logs", "version_0", 
            "checkpoints", checkpoint_name)

        return cls.load_from_checkpoint(
            checkpoint_loc,
            **model_args,
        )




    