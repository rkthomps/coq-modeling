import sys, os
import argparse
import time


def clean_search_waste(dir_loc: str) -> None:
    to_remove_paths: list[str] = []
    for root, _, files in os.walk(dir_loc):
        for file in files:
            no_underscores = file.lstrip("_")
            no_aux = no_underscores.lstrip("aux_")
            file_loc = os.path.join(root, file)
            seconds_since_modified = time.time() - os.path.getmtime(file_loc)
            days_since_modified = seconds_since_modified / (60 * 60 * 24)
            if (
                (len(no_aux) < len(file))
                and no_aux.endswith(".v")
                and no_aux in files
                and days_since_modified > 1
            ):
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

    args = parser.parse_args(sys.argv[1:])
    clean_search_waste(args.file_heirarchy_loc)
