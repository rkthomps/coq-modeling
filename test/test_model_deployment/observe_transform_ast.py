import os
import json
import time
import random
from tqdm import tqdm

from model_deployment.mine_goals import FileGoals, GoalRecord


def avg_dist(records: list[GoalRecord], sample_size: int = 100) -> float:
    sum_dist_time = 0
    count_dist_time = 0
    for i, goal_i in enumerate(records):
        for goal_j in records[(i + 1) :]:
            start = time.time()
            goal_i.term.distance(goal_j.term)
            end = time.time()
            print(end - start)
            sum_dist_time += end - start
            count_dist_time += 1
            if sample_size <= count_dist_time:
                return sum_dist_time / count_dist_time
    return sum_dist_time / count_dist_time


goal_loc = "proof-goals"

file_goals: list[FileGoals] = []
for file_name in tqdm(os.listdir(goal_loc)[:10]):
    goals = FileGoals.load(os.path.join(goal_loc, file_name))
    file_goals.append(goals)

all_records: list[GoalRecord] = []
for file_goal in file_goals:
    all_records.extend(file_goal.records)
random.seed(0)
random.shuffle(all_records)

print(avg_dist(all_records))
