@dataclass
class TestProofsConf:
    test_file: Path
    data_loc: Path
    sentence_db_loc: Path
    data_split_loc: Path
    theorem_name: str
    node_score_alias: str
    timeout: int
    branching_factor: int
    depth_limit: int
    max_expansions: int
    tactic_conf: TacticGenConf

    @classmethod
    def from_yaml(cls, yaml_data: Any) -> TestProofConf:
        return cls(
            Path(yaml_data["test_file"]),
            Path(yaml_data["data_loc"]),
            Path(yaml_data["sentence_db_loc"]),
            Path(yaml_data["data_split_loc"]),
            yaml_data["theorem_name"],
            yaml_data["node_score_alias"],
            yaml_data["timeout"],
            yaml_data["branching_factor"],
            yaml_data["depth_limit"],
            yaml_data["max_expansions"],
            tactic_gen_conf_from_yaml(yaml_data["tactic_conf"]),
        )
