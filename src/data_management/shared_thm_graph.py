from __future__ import annotations
from typing import Any, Optional

import sys, os
import pdb
import json
import argparse

from tqdm import tqdm

from data_management.dataset_file import DatasetFile


class FileGraph:
    def __init__(self, nodes: set[FileNode]) -> None:
        assert type(nodes) == set 
        assert all([type(n) == FileNode for n in nodes])
        self.nodes = nodes
        self.mapping = self.__get_id_mapping()

    def __get_id_mapping(self) -> dict[str, FileNode]:
        node_mapping: dict[str, FileNode] = {}
        for node in self.nodes:
            node_mapping[node.id()] = node
        return node_mapping

    def share_thm(self, node1_id: str, node2_id: str) -> bool:
        return node2_id in self.mapping[node1_id].neighbors


    def __get_component_seed_idx(self, work_list: list[FileNode], 
                                 all_seen_nodes: set[FileNode],
                                 start_idx: int) -> Optional[int]:
        for i, node in enumerate(work_list[start_idx:]):
            if node not in all_seen_nodes:
                return start_idx + i 
        return None


    def get_components(self) -> list[FileGraph]:
        all_seen_nodes: set[FileNode] = set()
        components: list[set[FileNode]] = []
        top_level_work_list = list(self.nodes)
        seed_idx = self.__get_component_seed_idx(
            top_level_work_list, all_seen_nodes, 0)
        while seed_idx is not None:
            component_seen_nodes: set[FileNode] = set()
            cur_node = top_level_work_list[seed_idx] 
            component_work_list = [cur_node]
            component_seen_nodes.add(cur_node)
            while len(component_work_list) > 0:
                cur_node = component_work_list.pop(0)
                node_neighbors = cur_node.node_neighbors(self.mapping)
                for neighbor in node_neighbors:
                    if neighbor in component_seen_nodes:
                        continue
                    component_seen_nodes.add(neighbor)
                    component_work_list.append(neighbor)
            components.append(component_seen_nodes)
            all_seen_nodes |= component_seen_nodes 
            seed_idx = self.__get_component_seed_idx(
                top_level_work_list, all_seen_nodes, seed_idx + 1)
        return [FileGraph(c) for c in components]


    def to_json(self) -> Any:
        return {"nodes": [n.to_json() for n in self.nodes]}

    def save(self, path: str) -> None:
        with open(path, "w") as fout:
            fout.write(json.dumps(self.to_json(), indent=2))


    @classmethod
    def from_json(cls, json_data: Any) -> FileGraph:
        nodes_data = json_data["nodes"]
        nodes: set[FileNode] = set()
        for node_data in nodes_data:
            node = FileNode.from_json(node_data)
            nodes.add(node)
        return cls(nodes)

    @classmethod
    def load(cls, path: str) -> FileGraph:
        with open(path, "r") as fin:
            json_data = json.load(fin)
            return cls.from_json(json_data)


class FileNode:
    def __init__(self, file_name: str, 
                 theorems: set[str],
                 neighbors: Optional[set[str]] = None) -> None:
        assert type(file_name) == str
        assert type(theorems) == set
        assert all([type(t) == str for t in theorems])
        self.file_name = file_name
        self.theorems = theorems

        if neighbors is None:
            self.neighbors: set[str] = set()
        else:
            assert type(neighbors) == set 
            assert all([type(n) == str for n in neighbors])
            self.neighbors = neighbors

    def meet_candidate_neighbor(self, other: FileNode) -> None:
        if len(self.theorems & other.theorems) > 0:
            self.neighbors.add(other.id())
            other.neighbors.add(self.id())

    def node_neighbors(self, mapping: dict[str, FileNode]) -> list[FileNode]:
        node_neigbor_list: list[FileNode] = []
        for n in self.neighbors:
            node_neigbor_list.append(mapping[n])
        return node_neigbor_list

    def id(self) -> str:
        return self.file_name

    def __hash__(self) -> int:
        return hash(self.file_name)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, FileNode):
            return False
        return hash(self) == hash(other)


    @classmethod
    def from_dset_obj(cls, file_dir_name: str, dset_obj: DatasetFile) -> FileNode:
        theorems: set[str] = set()
        for proof in dset_obj.proofs:
            theorems.add(proof.theorem.term.text)
        return cls(file_dir_name, theorems, set())


    def to_json(self) -> Any:
        assert self.neighbors is not None
        thm_list = list(self.theorems)
        neighbor_list = list(self.neighbors)
        return {
            "file_name": self.file_name,
            "thm_list": thm_list,
            "neighbor_list": neighbor_list,
        }

    @classmethod
    def from_json(cls, json_data: Any) -> FileNode:
        file_name = json_data["file_name"]
        thms = set(json_data["thm_list"])
        neighbors = set(json_data["neighbor_list"])
        return cls(file_name, thms, neighbors)


def create_and_save_shared_thm_graph(raw_data_loc: str, save_loc: str) -> None:
    nodes: set[FileNode] = set()
    print("Creating graph...")
    for project_name in tqdm(os.listdir(raw_data_loc)):
        project_loc = os.path.join(raw_data_loc, project_name)
        project_obj = DatasetFile.from_directory(project_loc)
        project_node = FileNode.from_dset_obj(project_name, project_obj) 
        nodes.add(project_node)

    print("Finding shared thms...")
    node_list = list(nodes)
    for i in tqdm(range(len(node_list))):
        for j in range(i + 1, len(node_list)):
            node_list[i].meet_candidate_neighbor(node_list[j])

    print("Saving graph...")
    file_graph = FileGraph(nodes)
    with open(save_loc, "w") as fout:
        fout.write(json.dumps(file_graph.to_json(), indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Create a graph of shared thms between files.")
    parser.add_argument("raw_data_loc", type=str, help="Location of raw data.")
    parser.add_argument("save_data_loc", type=str, help="Where to save resulting graph.")
    args = parser.parse_args(sys.argv[1:])
    if os.path.exists(args.save_data_loc):
        print(f"{args.save_data_loc} exists.", file=sys.stderr)
        exit(1)
    create_and_save_shared_thm_graph(args.raw_data_loc, args.save_data_loc)

