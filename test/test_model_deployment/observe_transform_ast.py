import os
import json
import time
import random
import cProfile
from tqdm import tqdm

from model_deployment.transform_ast import AdjTree
from model_deployment.mine_goals import FileGoals, GoalRecord


def dist_stree(records: list[GoalRecord]) -> float:
    distance_sum: int = 0
    distance_count: int = 0
    for i, goal_i in enumerate(records):
        for goal_j in records[(i + 1) :]:
            distance_sum += goal_i.term.distance(goal_j.term)
            distance_count += 1
    return distance_sum / distance_count

def set_dist_adjtree(records: list[GoalRecord]) -> float:
    distance_sum: int = 0
    distance_count: int = 0
    for i, goal_i in enumerate(records):
        at1 = AdjTree.from_stree(goal_i.term)
        for goal_j in records[(i + 1) :]:
            at2 = AdjTree.from_stree(goal_j.term)
            distance_sum += at1.fast_distance(at2)
            distance_count += 1
    return distance_sum / distance_count


def dist_adjtree(records: list[GoalRecord]) -> float:
    distance_sum: int = 0
    distance_count: int = 0
    for i, goal_i in enumerate(records):
        at1 = AdjTree.from_stree(goal_i.term)
        for goal_j in records[(i + 1) :]:
            at2 = AdjTree.from_stree(goal_j.term)
            distance_sum += at1.distance(at2)
            distance_count += 1
    return distance_sum / distance_count



goal_loc = "proof-goals"

file_goals: list[FileGoals] = []
for file_name in tqdm(os.listdir(goal_loc)[:10]):
    goals = FileGoals.load(os.path.join(goal_loc, file_name))
    file_goals.append(goals)

all_records: list[GoalRecord] = []
for file_goal in file_goals:
    all_records.extend(file_goal.records)

all_records = all_records[:200]
def profile_method():
    avg = dist_adjtree(all_records)

cProfile.run("profile_method()")

# start = time.time()
# avg = set_dist_adjtree(all_records)
# end = time.time()
# print("{:30s}: {:.2f}; Time: {:.2f}".format("Set Edist avg:", avg, end - start))


# start = time.time()
# avg = dist_adjtree(all_records)
# end = time.time()
# print("{:30s}: {:.2f}; Time: {:.2f}".format("Edist avg:", avg, end - start))

# start = time.time()
# avg = dist_stree(all_records)
# end = time.time()
# print("{:30s}: {:.2f}; Time: {:.2f}".format("Custom avg:", avg, end - start))

