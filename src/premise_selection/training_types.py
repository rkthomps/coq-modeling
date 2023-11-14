import torch
from dataclasses import dataclass


@dataclass
class PremiseBatch:
    context_ids: torch.Tensor
    context_mask: torch.Tensor
    prem_ids: torch.Tensor
    prem_mask: torch.Tensor
    label: torch.Tensor
