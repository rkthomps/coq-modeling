
import argparse

from sentence_db import SentenceDB, DBSentence
from dataset_file import DatasetFile, Sentence



if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("data_points_loc")
    parser.add_argument("db_loc")
    dp =  