
import sys, os
import argparse

import json

from model_deployment.searcher import ProofSearchTree


def build_html_document(search_tree: ProofSearchTree) -> str:

    # node_template = (
    #     f"<div class=\"node\" style=\"position: absolute; left: {left_pos}; right: {right_pos};\">" 
    #     f"  <p> {tactic} <\p>"
    #)
    


def show_search_tree(search_tree_loc: str) -> None:
    with open(search_tree_loc, "r") as fin:
        search_tree_data = json.load(fin) 
    search_tree = ProofSearchTree.from_json(search_tree_data)
    html_doc = build_html_document(search_tree)



if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Render a proof search tree in a browser.")
    parser.add_argument("search_tree_loc", help="Location of json-saved search tree")
    args = parser.parse_args(sys.argv[1:])
