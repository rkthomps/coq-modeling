
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

MODEL_LOC = "/home/ubuntu/coq-modeling/models/codellama-7b-basic"
CHECKPOINT_NUM = 200 

model_path = os.path.join(MODEL_LOC, f"checkpoint-{CHECKPOINT_NUM}")
model_conf = load_config(os.path.join(MODEL_LOC, CONF_NAME))

quantization_config = BitsAndBytesConfig(load_in_4bit=True)
model = LlamaForCausalLM.from_pretrained(
    model_path, quantization_config=quantization_config
)
tokenizer = get_tokenizer(model_conf) 
tokenizer.add_eos_token = False # Don't add eos to input during inference
max_input_len = model_conf["max_input_len"]
device = "cuda" 


@app.route("/codellama", methods=["POST"])
def codellama() -> str:
    example = LmExample.from_json(request.form)
    collated_in = collate_input(tokenizer, max_input_len, example.input)

    input_ids = tokenizer(collated_in, return_tensors="pt")["input_ids"].to("cuda")
    model_input = tokenizer.decode(input_ids[0])
    output = model.generate(
        input_ids,
        max_new_tokens=200,
    )
    output = output[0].to("cpu")

    only_output = tokenizer.decode(output[input_ids.shape[1]:], skip_special_tokens=True)
    response = {
        "input": model_input,
        "output": only_output,
    }
    return json.dumps(response, indent=2)


if __name__=="__main__":
    app.run(host="0.0.0.0", port=5000, debug=True, use_reloader=False)
