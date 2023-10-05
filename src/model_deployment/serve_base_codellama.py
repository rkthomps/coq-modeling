from __future__ import annotations
from typing import Any

import sys, os
import json
import argparse

from flask import Flask, request
from transformers import (LlamaForCausalLM, CodeLlamaTokenizer,
                          BitsAndBytesConfig, StoppingCriteria)
from transformers.generation.utils import BeamSearchDecoderOnlyOutput 
import torch 
from torch import LongTensor, FloatTensor

from tactic_gen.lm_example import LmExample 
from tactic_gen.train_codellama import (collate_input, CONF_NAME, load_config,
                                        get_tokenizer)


app = Flask(__name__) 

MODEL_NAME = "codellama/CodeLlama-7b-hf"

# quantization_config = BitsAndBytesConfig(load_in_4bit=True)
# model = LlamaForCausalLM.from_pretrained(
#     MODEL_NAME, quantization_config=quantization_config
# )
# tokenizer = CodeLlamaTokenizer.from_pretrained(MODEL_NAME) 
device = "cuda" 


class PeriodStoppingCriteria(StoppingCriteria):
    def __init__(self, stop_tok_ids: list[int]) -> None:
        self.stop_tok_ids = stop_tok_ids
        self.num_input_periods = torch.tensor(0).to(device)

    def set_num_periods(self, input_ids: LongTensor) -> None:
        self.num_input_periods = self.get_num_periods(input_ids)[0]

    def get_num_periods(self, input_ids: LongTensor) -> torch.Tensor:
        start_shape = (input_ids.shape[0],)
        sum_input_periods = torch.full(start_shape, fill_value=0).to(device)
        for stop_tok_id in self.stop_tok_ids:
            sum_input_periods += (input_ids == stop_tok_id).sum(axis=1)
        return sum_input_periods

    def __call__(self, input_ids: LongTensor, scores: FloatTensor, **kwargs: Any) -> bool:
        return bool((self.get_num_periods(input_ids) > self.num_input_periods).all())

    @classmethod
    def from_tokenizer(cls, tokenizer: CodeLlamaTokenizer) -> PeriodStoppingCriteria:
        period_tok_ids: list[int] = []
        for token, token_id in tokenizer.get_vocab().items():
            if "." in token:
                period_tok_ids.append(token_id)
        return cls(period_tok_ids)


@app.route("/codellama", methods=["POST"])
def codellama() -> str:
    n = int(request.form["n"])
    example = LmExample.from_json(request.form)

    input_ids = tokenizer(example.input, return_tensors="pt")["input_ids"].to("cuda")
    model_input = tokenizer.decode(input_ids[0])
    print(model_input)
    output = model.generate(
        input_ids,
        num_beams=n,
        num_return_sequences=n,
        max_new_tokens=32,
        output_scores=True,
        return_dict_in_generate=True,
        pad_token_id=tokenizer.pad_token_id,
    )
    assert type(output) == BeamSearchDecoderOnlyOutput 
    num_padding_tokens = (output.sequences == tokenizer.pad_token_id).sum(axis=1)
    seq_lens = (output.sequences.shape[1] - input_ids.shape[1] - num_padding_tokens).to("cpu")
    tactics = tokenizer.batch_decode(output.sequences[:, input_ids.shape[1]:], skip_special_tokens=True) 
    scores = (output.sequences_scores).to("cpu")
    del output

    response = {
        "tactics": list(tactics),
        "scores": scores.tolist(),
        "num_tokens": seq_lens.tolist(),
    }
    print(response)
    return json.dumps(response, indent=2)


if __name__=="__main__":
    parser = argparse.ArgumentParser(description="Start a server running CodeLLama")    
    parser.add_argument("port", type=int, help="Port on which to run the server.")
    args = parser.parse_args(sys.argv[1:])
    app.run(host="0.0.0.0", port=args.port, debug=True, use_reloader=False)
