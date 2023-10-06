
import sys, os
import json
import argparse

from flask import Flask, request
from transformers import (LlamaForCausalLM, CodeLlamaTokenizer,
                          BitsAndBytesConfig)
from transformers.generation.utils import BeamSearchDecoderOnlyOutput 
import torch

from tactic_gen.lm_example import LmExample 
from tactic_gen.train_codellama import (collate_input, CONF_NAME, load_config,
                                        get_tokenizer)
from model_deployment.serve_codellama_utils import (
    PeriodStoppingCriteria, do_sample, SampleResult)


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


# @app.route("/codellama", methods=["POST"])
# def codellama() -> str:
#     n = int(request.form["n"])
#     example = LmExample.from_json(request.form)

#     input_ids = tokenizer(example.input, return_tensors="pt")["input_ids"].to("cuda")
#     model_input = tokenizer.decode(input_ids[0])
#     print(model_input)

#     period_stopping.set_num_periods(input_ids)
#     stopping_list = StoppingCriteriaList([period_stopping])
#     tactics: list[str] = []
#     scores: list[float] = []
#     num_tokens: list[int] = []
#     for i in range(n):
#         output = model.generate(
#             input_ids,
#             temperature=1,
#             do_sample=True,
#             max_new_tokens=32,
#             output_scores=True,
#             return_dict_in_generate=True,
#             stopping_criteria=stopping_list,
#         )
#         assert type(output) == SampleDecoderOnlyOutput 
#         output_sequence = output.sequences[0]
#         input_sequence = input_ids[0]
#         output_length = len(output.scores)
#         tactic = tokenizer.decode(output_sequence[len(input_sequence):], skip_special_tokens=True)
#         score = get_sequence_score(input_sequence, output_sequence, output.scores, period_stopping)
#         tactics.append(tactic)
#         scores.append(score)
#         num_tokens.append(output_length)
#         del output

#     response = {
#         "tactics": tactics,
#         "scores": scores,
#         "num_tokens": num_tokens,
#     }
#     print(response)
#     return json.dumps(response, indent=2)


period_stopping = PeriodStoppingCriteria.from_tokenizer(tokenizer)

@app.route("/codellama", methods=["POST"])
def codellama() -> str:
    n = int(request.form["n"])
    example = LmExample.from_json(request.form)
    collated_in = collate_input(tokenizer, max_input_len, example.input)

    input_ids = tokenizer(collated_in, return_tensors="pt")["input_ids"].to("cuda")
    model_input = tokenizer.decode(input_ids[0])
    print(model_input)

    sample_result = do_sample(input_ids, model, tokenizer, n, period_stopping)

    return json.dumps(sample_result.to_json(), indent=2)

if __name__=="__main__":
    parser = argparse.ArgumentParser(description="Start a server running CodeLLama")    
    parser.add_argument("port", type=int, help="Port on which to run the server.")
    args = parser.parse_args(sys.argv[1:])
    app.run(host="0.0.0.0", port=args.port, debug=True, use_reloader=False)
