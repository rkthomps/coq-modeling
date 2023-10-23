import sys, os
import argparse

from evaluation.compile_corpus import clean_directory


def recursive_clean_directory(dir_loc: str) -> None:
    clean_directory(dir_loc)
    for subfile in os.listdir(dir_loc):
        subfile_loc = os.path.join(dir_loc, subfile)
        if os.path.isdir(subfile_loc):
            recursive_clean_directory(subfile_loc)


def clean_search_waste(dir_loc: str) -> None:
    to_remove_paths: list[str] = []
    for root, _, files in os.walk(dir_loc):
        for file in files:
            no_underscores = file.lstrip("_")
            no_aux = no_underscores.lstrip("aux_")
            if (len(no_aux) < len(file)) and no_aux.endswith(".v") and no_aux in files:
                to_remove_paths.append(os.path.join(root, file))
    print("Removing: ", to_remove_paths)
    for remove_path in to_remove_paths:
        os.remove(remove_path)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "Clean coq file and makefile junk from file heirarchy."
    )
    parser.add_argument(
        "file_heirarchy_loc", type=str, help="Location of file heirarchy."
    )
    parser.add_argument(
        "action",
        type=str,
        help=(
            "<clean | deep-clean>. clean removes search materials. "
            "deep-clean removes compile materials."
        ),
    )
    args = parser.parse_args(sys.argv[1:])
    if args.action == "clean":
        clean_search_waste(args.file_heirarchy_loc)
    elif args.action == "deep-clean":
        recursive_clean_directory(args.file_heirarchy_loc)
        clean_search_waste(args.file_heirarchy_loc)
    else:
        raise ValueError(
            (
                f"Didn't recognize argument {args.action} must be "
                '"clean" or "deep-clean".'
            )
        )
