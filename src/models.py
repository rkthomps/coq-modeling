
from typing import Any, Optional

import pytorch_lightning as pl
import torch
from pytorch_lightning.utilities.types import STEP_OUTPUT 
from transformers import T5ForConditionalGeneration, AutoTokenizer # Todo - what are these. 

class BasicModel(pl.LightningModule):
    def __init__(self, model_name: str) -> None:
        super(BasicModel, self).__init__()
        self.model_name = model_name
        self.model = T5ForConditionalGeneration.from_pretrained(model_name)
        self.tokenizer = AutoTokenizer.from_pretrained(model_name)

    def forward(self, input: str) -> torch.Tensor:
        return super().forward(*args, **kwargs)

    def training_step(self, batch, batch_idx) -> STEP_OUTPUT:
        pass

    def validation_step(self, *args: Any, **kwargs: Any) -> STEP_OUTPUT | None:
        return super().validation_step(*args, **kwargs)

    def test_step(self, *args: Any, **kwargs: Any) -> STEP_OUTPUT | None:
        return super().test_step(*args, **kwargs)

    def predict_step(self, batch: Any, batch_idx: int, dataloader_idx: int = 0) -> Any:
        return super().predict_step(batch, batch_idx, dataloader_idx)

    def configure_optimizers(self) -> Any:
        return super().configure_optimizers()


