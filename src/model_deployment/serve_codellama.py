
import sys, os
import json

from flask import Flask, request
from transformers import (LlamaForCausalLM, CodeLlamaTokenizer,
                          BitsAndBytesConfig)
from transformers.generation.utils import BeamSearchDecoderOnlyOutput 
import torch

from tactic_gen.lm_example import LmExample 
from tactic_gen.train_codellama import (collate_input, CONF_NAME, load_config,
                                        get_tokenizer)


app = Flask(__name__) 

MODEL_LOC = "/home/ubuntu/coq-modeling/models/codellama-7b-basic"
CHECKPOINT_NUM = 20500 

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
    n = int(request.form["n"])
    example = LmExample.from_json(request.form)
    collated_in = collate_input(tokenizer, max_input_len, example.input)

    input_ids = tokenizer(collated_in, return_tensors="pt")["input_ids"].to("cuda")
    model_input = tokenizer.decode(input_ids[0])
    print(model_input)
    output = model.generate(
        input_ids,
        num_beams=n,
        num_return_sequences=n,
        max_new_tokens=64,
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
    app.run(host="0.0.0.0", port=5000, debug=True, use_reloader=False)