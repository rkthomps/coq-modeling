
import torch

class PremiseBatch:
    def __init__(self, 
                 context_ids: torch.Tensor,
                 context_mask: torch.Tensor,
                 prem_ids: torch.Tensor,
                 prem_mask: torch.Tensor,
                 label: torch.Tensor):
        assert type(context_ids) == torch.Tensor
        assert type(context_mask) == torch.Tensor
        assert type(prem_ids) == torch.Tensor
        assert type(prem_mask) == torch.Tensor
        assert type(label) == torch.Tensor
        self.context_ids = context_ids
        self.context_mask = context_mask
        self.prem_ids = prem_ids
        self.prem_mask = prem_mask
        self.label = label
