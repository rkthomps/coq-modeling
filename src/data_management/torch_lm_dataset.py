
from torch.utils.data import Dataset
from transformers import AutoTokenizer

class CoqLmDataset(Dataset):
    def __init__(self, dataset_file: str, 
                 tokenizer: ByT5Tokenizer,
                 max_seq_len: int) -> None:
        super().__init__()
        self.dataset_file = dataset_file
        assert os.path.exists(self.dataset_file)
        assert self.dataset_file.endswith("shuffled.jsonl")
        self.tokenizer = tokenizer 
        self.max_seq_len = max_seq_len
        self.data: list[LmExample] = []
        with jsonlines.open(self.dataset_file) as fin:
            for obj in fin:
                example = LmExample.from_json(obj) 
                self.data.append(example)

    def __getitem__(self, index: int) -> LmExample:
        return self.data[index]

    def __len__(self) -> int:
        return len(self.data)