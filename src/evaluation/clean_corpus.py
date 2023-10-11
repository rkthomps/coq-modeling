
import sys, os
import argparse

from evaluation.compile_corpus import clean_directory 

def recursive_clean_directory(dir_loc: str) -> None:
    clean_directory(dir_loc)
    for subfile in os.listdir(dir_loc):
        subfile_loc = os.path.join(dir_loc, subfile)
        if os.path.isdir(subfile_loc):
            recursive_clean_directory(subfile_loc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Clean coq file and makefile junk from file heirarchy.")
    parser.add_argument("file_heirarchy_loc", type=str,
                        help="Location of file heirarchy.")
    args = parser.parse_args(sys.argv[1:])
    recursive_clean_directory(args.file_heirarchy_loc)

