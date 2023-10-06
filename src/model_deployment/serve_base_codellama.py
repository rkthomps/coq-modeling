from __future__ import annotations
from typing import Any

import sys, os
import json
import argparse

from flask import Flask, request
from transformers import (LlamaForCausalLM, CodeLlamaTokenizer,
                          BitsAndBytesConfig)
import torch 
from torch import LongTensor, FloatTensor

from tactic_gen.lm_example import LmExample 
from tactic_gen.train_codellama import (collate_input, TRAINING_CONF_NAME, load_config,
                                        get_tokenizer)
from model_deployment.serve_codellama_utils import (
    do_sample, SampleResult, PeriodStoppingCriteria)


app = Flask(__name__) 

MODEL_NAME = "codellama/CodeLlama-7b-hf"

quantization_config = BitsAndBytesConfig(load_in_4bit=True)
model = LlamaForCausalLM.from_pretrained(
    MODEL_NAME, quantization_config=quantization_config
)
tokenizer = CodeLlamaTokenizer.from_pretrained(MODEL_NAME) 
device = "cuda" 



period_stopping = PeriodStoppingCriteria.from_tokenizer(tokenizer)

@app.route("/codellama", methods=["POST"])
def codellama() -> str:
    n = int(request.form["n"])
    example = LmExample.from_json(request.form)

    input_ids = tokenizer(example.input, return_tensors="pt")["input_ids"].to("cuda")
    model_input = tokenizer.decode(input_ids[0])
    print(model_input)

    sample_result = do_sample(
        input_ids, model, tokenizer, n, period_stopping)
    
    return json.dumps(sample_result.to_json(), indent=2)



if __name__=="__main__":
    parser = argparse.ArgumentParser(description="Start a server running CodeLLama")    
    parser.add_argument("port", type=int, help="Port on which to run the server.")
    args = parser.parse_args(sys.argv[1:])
    app.run(host="0.0.0.0", port=args.port, debug=True, use_reloader=False)
