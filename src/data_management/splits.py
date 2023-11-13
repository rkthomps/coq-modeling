"""
Given a folder with a bunch of repositories, 
create a project-wise split according to time. 
"""

import argparse

class DataSplit:
    def __init__(self, train_projects: list[str], val_projects: list[str], test_projects: list[str]) -> None:
        self.train_projects = train_projects
        self.val_projects = val_projects
        self.test_projects = test_projects


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Create a train/val/test split.")

