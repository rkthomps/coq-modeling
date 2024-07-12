from pathlib import Path
from sqlite3 import connect, Connection, Cursor
from data_management.dataset_file import Sentence, Proof, Goal


class PremiseIndex:
    IDX_NAME = "premise"
    def get_idx(self, sentence: Sentence) -> int:
        pass


class ProofScriptIndex:
    IDX_NAME = "proof_script"
    def get_idx(self, proof: Proof) -> int:
        pass


class ProofStateIndex:
    IDX_NAME = "proof_state"
    def get_idx(self, goal: Goal) -> int:
        pass


DataIndex = PremiseIndex | ProofScriptIndex | ProofStateIndex


class TextDB:
    def __init__(self, connection: Connection, cursor: Cursor, table_name: str):
        self.connection = connection
        self.cursor = cursor
        self.table_name = table_name
    

    def insert_examples(self, examples: list[tuple[str,]]) -> list[int]:
        result = self.cursor.executemany(
            f"""
            INSERT INTO {self.table_name}  (text) VALUES
            (?)
            RETURNING id
            """,
            examples,
        ).fetchall()
        self.connection.commit()

        if len(result) != len(examples):
            raise ValueError(
                f"Something went wrong in query. Got {len(result)} after insert."
            )
        



def create_table(path: Path, table_name: str) -> tuple[Connection, Cursor]:
    if path.exists():
        raise ValueError(f"Table {table_name} already exists in {path}.")
    con = connect(path)
    cur = con.cursor()
    cur.execute(
        f"""
        CREATE TABLE {table_name} (
            id INTEGER PRIMARY KEY,
            text TEXT,
        )
        """
    )
    return con, cur
    

def index_corpus

