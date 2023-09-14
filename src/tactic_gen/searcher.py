
import sys, os
import shutil

class Searcher:
    SEARCH_TOKEN = "<prove>"

    def __init__(self, file_path: str) -> None:
        file_dir = os.path.dirname(file_path) 
        self.search_dir_path = self.__get_fresh_path(file_dir, ".proof-search")
        self.hidden_file_path = self.__get_fresh_path(file_dir, os.path.basename(file_path))

        shutil.copy(file_path, self.hidden_file_path)


    def __get_file_prefix(self):


    @classmethod
    def __get_fresh_path(cls, dirname: str, fresh_base: str) -> str:
        name = fresh_base 
        while os.path.exists(os.path.join(dirname, name)):
            name += "_"
        return os.path.join(dirname, name)


