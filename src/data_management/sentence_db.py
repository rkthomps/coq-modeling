from __future__ import annotations
from typing import Optional
import sys, os
import time
import ipdb
import functools

from dataclasses import dataclass
from sqlite3 import connect, Connection, Cursor


@dataclass(frozen=True)
class DBSentence:
    text: str
    file_path: str
    module: str
    sentence_type: str
    line: int


class SentenceDB:
    TABLE_NAME = "sentence"

    def __init__(self, connection: Connection, cursor: Cursor) -> None:
        self.connection = connection
        self.cursor = cursor
        self.__found_cache: dict[DBSentence, int] = {}
        self.__contains_cache: dict[int, bool] = {}

    def contains_id(self, id: int) -> bool:
        if id in self.__contains_cache:
            return self.__contains_cache[id]
        result = self.cursor.execute(
            f"""
            SELECT * FROM {self.TABLE_NAME} WHERE id={id}
                            """
        ).fetchall()
        if 0 == len(result):
            return False
        else:
            self.__contains_cache[id] = True
            return True

    def find_sentence(self, sentence: DBSentence) -> Optional[int]:
        if sentence in self.__found_cache:
            return self.__found_cache[sentence]

        result = self.cursor.execute(
            f"""
            SELECT id FROM {self.TABLE_NAME}
            WHERE
            text=? AND
            file_path=? AND
            module=? AND
            sentence_type=? AND
            line=?""",
            (
                sentence.text,
                sentence.file_path,
                sentence.module,
                sentence.sentence_type,
                sentence.line,
            ),
        ).fetchall()
        if 0 == len(result):
            return None
        if 1 == len(result):
            (resulting_id,) = result[0]
            self.__found_cache[sentence] = resulting_id
            return resulting_id
        raise ValueError(f"DB has more than one instance of {sentence}")


    @functools.lru_cache(10000)
    def insert_sentence(self, sentence: DBSentence) -> int:
        found_id = self.find_sentence(sentence)
        if found_id is not None:
            return found_id

        result = self.cursor.execute(
            f"""
            INSERT INTO {self.TABLE_NAME}  (text, file_path, module, sentence_type, line) VALUES
            (?, ?, ?, ?, ?)
            RETURNING id""",
            (
                sentence.text,
                sentence.file_path,
                sentence.module,
                sentence.sentence_type,
                sentence.line,
            ),
        ).fetchall()
        self.connection.commit()

        if len(result) != 1:
            raise ValueError(
                f"Something went wrong in query. Got {len(result)} after insert."
            )
        (resulting_id,) = result[0]
        return resulting_id
    
    def size(self) -> int:
        result = self.cursor.execute(
            f"""
            SELECT COUNT(*) FROM {self.TABLE_NAME}
                            """
        ).fetchall()
        if len(result) != 1:
            raise ValueError(
                "Problem executing size query."
            )
        (count,) = result[0]
        return count


    @functools.lru_cache(10000)
    def retrieve(self, id: int) -> DBSentence:
        result = self.cursor.execute(
            f"""
            SELECT * FROM {self.TABLE_NAME} WHERE id=?
                            """, (id, )
        ).fetchall()
        if len(result) != 1:
            raise ValueError(
                f"Expected single result from sentence db. Got {len(result)}"
            )
        _, text, file_path, module, sentence_type, line = result[0]
        return DBSentence(text, file_path, module, sentence_type, line)
    
    def commit(self) -> None:
        self.connection.commit()

    def close(self) -> None:
        self.cursor.close()
        self.connection.close()

    @classmethod
    def load(cls, db_path: str) -> SentenceDB:
        if not os.path.exists(db_path):
            raise ValueError(f"Database {db_path} does not exis does not exist.")
        con = connect(
            db_path,
        )
        cur = con.cursor()
        return cls(con, cur)

    @classmethod
    def create(cls, db_path: str) -> SentenceDB:
        if os.path.exists(db_path):
            raise ValueError(f"DB {db_path} already exists")
        con = connect(db_path)
        cur = con.cursor()
        cur.execute(
            f"""
            CREATE TABLE {cls.TABLE_NAME} (
                id INTEGER PRIMARY KEY, 
                text TEXT, 
                file_path TEXT, 
                module TEXT, 
                sentence_type TEXT, 
                line INTEGER)
        """
        )
        cur.execute(
            f"""
            CREATE INDEX text_index ON {cls.TABLE_NAME}(text)
        """
        )
        return cls(con, cur)
