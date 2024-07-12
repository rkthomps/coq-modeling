import torch


class Retriever(torch.nn.Module):
    def __init__(
        self, document_encoder: torch.nn.Module, query_encoder: torch.nn.Module
    ):
        super(Retriever, self).__init__()
        self.document_encoder = document_encoder
        self.query_encoder = query_encoder
