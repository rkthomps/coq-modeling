
import sys, os
import json

from flask import Flask, request
from transformers import (LlamaForCausalLM, CodeLlamaTokenizer,
                          BitsAndBytesConfig)
import torch

from data_management.lm_example import LmExample 
from tactic_gen.train_codellama import (collate_input, CONF_NAME, load_config,
                                        get_tokenizer)


app = Flask(__name__) 

MODEL_LOC = "/home/ubuntu/coq-modeling/models/codellama-7b-hf-test/checkpoint-1100"
model_conf = load_config(os.path.join(MODEL_LOC, CONF_NAME))

quantization_config = BitsAndBytesConfig(load_in_4bit=True)
model = LlamaForCausalLM.from_pretrained(
    MODEL_LOC, quantization_config=quantization_config
)
tokenizer = get_tokenizer(model_conf) 
device = "cuda" 


@app.route("/codellama", methods=["POST"])
def codellama() -> str:
    example = LmExample.from_json(request.form)
    collated_in = collate_input(example.input)
    inputs = tokenizer.encode(collated_in, return_tensors="pt").to(device)
    outputs = model.generate(inputs)
    pretty_out = tokenizer.decode(outputs[0])
    response = {
        "output": pretty_out
    }
    return json.dumps(response, indent=2)


if __name__=="__main__":
    app.run(host="0.0.0.0", port=5000, debug=True, use_reloader=False)