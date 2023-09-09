
from typing import Any, Optional

import pytorch_lightning as pl
import torch
from pytorch_lightning.utilities.types import STEP_OUTPUT 
from transformers import T5ForConditionalGeneration, AutoTokenizer # Todo - what are these. 

from datamodule import Batch

class BasicModel(pl.LightningModule):
    def __init__(self, model_name: str,
                 lr: float,
                 warmup_steps: int) -> None:
        super(BasicModel, self).__init__()
        self.model_name = model_name
        self.lr = lr
        self.warmup_steps = warmup_steps
        self.model = T5ForConditionalGeneration.from_pretrained(model_name)
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)

    def forward(self,
                input_ids: torch.Tensor,
                input_mask: torch.Tensor,
                output_ids: torch.Tensor,
                ) -> torch.Tensor:
        return self.model(
            input_ids=input_ids,
            attention_mask=input_mask,
            labels=output_ids,
        ).loss


    def training_step(self, batch: Batch, batch_idx: int) -> STEP_OUTPUT:
        loss = self(batch["input_ids"], 
                    batch["input_mask"], 
                    batch["output_ids"])
        return loss

    def validation_step(self, *args: Any, **kwargs: Any) -> STEP_OUTPUT | None:
        raise NotImplementedError

    def test_step(self, *args: Any, **kwargs: Any) -> STEP_OUTPUT | None:
        raise NotImplementedError

    def predict_step(self, batch: Any, batch_idx: int, dataloader_idx: int = 0) -> Any:
        raise NotImplementedError

    def configure_optimizers(self) -> Any:
        raise NotImplementedError


