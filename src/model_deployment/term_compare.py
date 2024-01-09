from coqpyt.coq.base_file import CoqFile, GoalAnswer
from data_management.splits import DataSplit, FileInfo


"""

I want to get the proof for the current goal. 
Is it true that the current goal is solved when  

len(all goals) = 1 - len(current goal) ? 

"""


def get_var_to_generalize(goals: GoalAnswer) -> str:
    pass


def get_normal_form(aux_file_path: str, workspace_path: str, file_prefix: str):
    with open(aux_file_path, "w") as fout:
        fout.write(file_prefix)

    with CoqFile(aux_file_path, workspace=workspace_path) as coq_file:
        coq_file.run()
        goals = coq_file.current_goals
        assert goals is not None
