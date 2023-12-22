import os

from data_management.splits import FileInfo
from evaluation.evaluate import Evaluator
from evaluation.eval_set import FileListEvalSet
from model_deployment.model_wrapper import wrapper_from_conf
from model_deployment.node_score import TokenLengthNormalizedScore


results_loc = os.path.join("test", "test_files", "test-eval")
eval_temp_dir = os.path.join(results_loc, "tmp")

file_list = [FileInfo("examples-list.v", "examples/list.v", "examples", "examples")]

model_wrapper = wrapper_from_conf(
    {
        "alias": "local",
        "pretrained-name": "/home/ubuntu/coq-modeling/models/codellama-7b-basic-rnd-split-rnd-samp-2/checkpoint-7459",
    }
)

node_score_type = TokenLengthNormalizedScore

eval_set = FileListEvalSet(".", eval_temp_dir, file_list, 0)

timeout = 240
branching_factor = 4
max_leaf_expansions = 50

evaluator = Evaluator(
    results_loc,
    eval_set,
    timeout,
    branching_factor,
    max_leaf_expansions,
    model_wrapper,
    node_score_type,
)

evaluator.evaluate()
