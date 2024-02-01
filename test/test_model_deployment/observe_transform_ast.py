import os
import json

from coqpyt.coq.base_file import CoqFile
import ipdb

from model_deployment.transform_ast import term_from_ast, get_body_from_definition

test_path = "tmp.v"
test_step = 0


with CoqFile(os.path.abspath(test_path)) as coq_file:
    ast = coq_file.steps[test_step].ast.span

ast_no_def = get_body_from_definition(ast)

ipdb.set_trace()
term = term_from_ast(ast_no_def)

print(term.to_strtree().to_string())
