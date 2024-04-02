import argparse
import sys, os
import subprocess
import traceback
import csv
import ipdb
from util.util import LOGGER

from dataclasses import dataclass
from coqpyt.coq.base_file import CoqFile

COQ_CRAWLER_LOC = "coq-crawler"
if not COQ_CRAWLER_LOC in sys.path:
    sys.path.insert(0, COQ_CRAWLER_LOC)

COQ_PYT_LOC = os.path.join("coqpyt", "coqpyt")
if not COQ_PYT_LOC in sys.path:
    sys.path.insert(0, COQ_PYT_LOC)

from project import Project, ValidFile


def print_command_error(cmd: list[str]) -> None:
    cmd_str = " ".join(cmd)
    print("Problem running", f'"{cmd_str}"')


def run_command(cmd: list[str], shell: bool = False) -> None:
    command_str = " ".join(cmd)
    print("Running command:", command_str)
    cmd_result = subprocess.run(cmd, shell=shell)
    if cmd_result.returncode != 0:
        raise RuntimeError(f"Could not run command: {command_str}")


@dataclass(frozen=True)
class TestProject:
    org: str
    name: str
    install_commands: list[list[str]]

    def __get_install_name(self) -> str:
        return f"{self.org}-{self.name}"

    def __get_switch_name(self) -> str:
        return f"{self.org}-{self.name}"

    def set_opam_switch(self) -> None:
        local_switch_name = os.path.join(".", self.__get_switch_name())
        if not os.path.exists(local_switch_name):
            create_switch_command = ["opam", "switch", "create", local_switch_name]
            run_command(create_switch_command)

        set_switch_command = [
            "eval",
            f"$(opam env --switch={local_switch_name} --set-switch)",
        ]
        run_command(set_switch_command, shell=True)

        install_coq_command = ["opam", "pin", "add", "coq", "8.18.0", "--yes"]
        run_command(install_coq_command)

        install_coq_released = [
            "opam",
            "repo",
            "add",
            "coq-released",
            "--yes",
            "https://coq.inria.fr/opam/released",
        ]
        run_command(install_coq_released)

        install_coq_lsp_command = ["opam", "install", "coq-lsp"]
        run_command(install_coq_lsp_command)

    def __is_valid(self, file: str, workspace: str) -> bool:
        file_loc = os.path.abspath(file)
        workspace_loc = os.path.abspath(workspace)
        assert file.endswith(".v")
        file_base = file[: (-1 * len(".v"))]
        with CoqFile(file_loc, workspace=workspace_loc, timeout=256) as coq_file:
            if coq_file.is_valid:
                if not os.path.exists(file_base + ".vo"):
                    coq_file.save_vo()
                return True
            return False

    def get_valid_files(self, repo_dir: str) -> list[ValidFile]:
        valid_files: list[ValidFile] = []
        abs_repo = os.path.abspath(repo_dir)
        for dirpath, _, filenames in os.walk(abs_repo):
            for filename in filenames:
                file_path = os.path.join(dirpath, filename)
                relpath = os.path.relpath(file_path, abs_repo)
                if filename.endswith(".v"):
                    try:
                        is_valid = self.__is_valid(file_path, abs_repo)
                        if is_valid:
                            valid_files.append(ValidFile(relpath, abs_repo))
                        else:
                            LOGGER.warning(f"File {relpath} was not valid.")
                    except:
                        traceback.print_exc()
                        LOGGER.warning(f"File {relpath} got timeout or oom error.")

        return valid_files

    def write_valid_files(self, repo_dir: str, files: list[ValidFile]) -> None:
        with open(os.path.join(repo_dir, "valid_files.csv"), "w") as fout:
            csv.writer(fout).writerows(files)

    def install(self, install_dir: str) -> None:
        cur_dir = os.path.abspath(os.curdir)
        install_name = self.__get_install_name()
        try:
            os.chdir(install_dir)
            if not os.path.exists(install_name):
                clone_command = [
                    "git",
                    "clone",
                    "--recurse-submodules",
                    f"git@github.com:{self.org}/{self.name}",
                    install_name,
                ]
                run_command(clone_command)

            os.chdir(install_name)
            # self.set_opam_switch()
            for instr in self.install_commands:
                run_command(instr)
            valid_files = self.get_valid_files(".")
            self.write_valid_files(".", valid_files)
        finally:
            os.chdir(cur_dir)


projects = {
    "hydra-battles": TestProject(
        "coq-community",
        "hydra-battles",
        [
            ["opam", "install", "coq-equations", "--yes"],
            ["opam", "install", "coq-hydra-battles", "--yes"],
            ["opam", "install", "coq-addition-chains", "--yes"],
            ["opam", "install", "coq-gaia-hydras", "--yes"],
            ["opam", "install", "coq-goedel", "--yes"],
            ["make"],
        ],
    ),
    "coq-ext-lib": TestProject(
        "coq-community",
        "coq-ext-lib",
        [
            ["make", "theories"],
        ],
    ),
    "reglang": TestProject(
        "coq-community",
        "reglang",
        [
            ["make"],
        ],
    ),
    "bignums": TestProject(
        "coq-community",
        "bignums",
        [
            ["make"],
        ],
    ),
    "corn": TestProject(
        "coq-community",
        "corn",
        [
            ["opam", "install", "coq-math-classes", "--yes"],
            ["opam", "install", "coq-bignums", "--yes"],
            ["./configure.sh"],
            ["make"],
        ],
    ),
    "fourcolor": TestProject(
        "coq-community",
        "fourcolor",
        [
            ["make"],
        ],
    ),
    "gaia": TestProject("coq-community", "gaia", [["make"]]),
    "math-classes": TestProject(
        "coq-community",
        "math-classes",
        [
            ["./configure.sh"],
            ["make"],
        ],
    ),
    "huffman": TestProject(
        "coq-community",
        "huffman",
        [
            ["make"],
        ],
    ),
    "compcert": TestProject(
        "AbsInt",
        "CompCert",
        [
            ["./configure", "--ignore-coq-version", "x86_64-linux"],
            ["make"],
        ],
    ),
    "sudoku": TestProject(
        "coq-community",
        "sudoku",
        [["make"]],
    ),
    "bertrand": TestProject(
        "coq-community",
        "bertrand",
        [["make"]],
    ),
    "graph-theory": TestProject(
        "coq-community",
        "graph-theory",
        [["make"]],
    ),
    "stalmarck": TestProject("coq-community", "stalmarck", [["make"]]),
    "qarith-stern-brocot": TestProject(
        "coq-community",
        "qarith-stern-brocot",
        [["make"]],
    ),
    "parseque": TestProject("coq-community", "parseque", [["make"]]),
    "atbr": TestProject("coq-community", "atbr", [["make"]]),
    "reduction-effects": TestProject("coq-community", "reduction-effects", [["make"]]),
    "coqeal": TestProject("coq-community", "coqeal", [["make"]]),

    # Coqgym
    "weak-up-to": TestProject("coq-contribs", "weak-up-to", [["make"]]),
    "buchberger": TestProject("coq-community", "buchberger", [["make"]]),
    "jordan-curve-theorem": TestProject("coq-contribs", "jordan-curve-theorem", [["make"]]),
    "dblib": TestProject("coq-community", "dblib", [["make"]]),
    "disel": TestProject("DistributedComponents", "disel", [["make"]]),
    "zchinese": TestProject("coq-contribs", "zchinese", [["make"]]),
    "zfc": TestProject("coq-contribs", "zfc", [["make"]]),
    "dep-map": TestProject("coq-contribs", "dep-map", [["make"]]),
    "chinese": TestProject("coq-contribs", "chinese", [["make"]]),
    "unifysl": TestProject("QinxiangCao", "UnifySL", [["make"]]),
    "hoare-tut": TestProject("coq-community", "hoare-tut", [["make"]]),
    "poltac": TestProject("thery", "PolTac", [["make", "all"]]),
    "angles": TestProject("coq-contribs", "angles", [["make"]]),
    "coq-procrastination": TestProject("Armael", "coq-procrastination", [["make"]]),
    "tree-automata": TestProject("coq-contribs", "tree-automata", [["make"]]),
    "coquelicot": TestProject("thery", "coquelicot", [["./configure"], ["make", "-f", "Remakefile"]]),
    "fermat4": TestProject("coq-contribs", "fermat4", [["make"]]),
    "coqoban": TestProject("coq-community", "coqoban", [["make"]]),
    "goedel": TestProject("coq-community", "goedel", [["make"]]),
    "verdi-raft": TestProject("uwplse", "verdi-raft", [["make"]]),
    "verdi": TestProject("uwplse", "verdi", [["make"]]),
    "zorns-lemma": TestProject("coq-community", "zorns-lemma", [["make"]]),
    "coqrel": TestProject("CertiKOS", "coqrel", [["./configure"], ["make"]]),
    "fundamental-arithmetics": TestProject("coq-contribs", "fundamental-arithmetics", [["make"]]),

}


def display_alias_options() -> None:
    for alias, project in projects.items():
        line = f"{alias}: {project.org}/{project.name}"
        print(line)


if __name__ == "__main__":
    parser = argparse.ArgumentParser("Compile a project into a specified directory.")
    subparsers = parser.add_subparsers()

    # List options
    list_parser = subparsers.add_parser("list", help="List project aliases.")

    # Compile projects
    compile_parser = subparsers.add_parser(
        "compile", help="Download and compile a project"
    )
    compile_parser.add_argument(
        "compile_destination",
        help="Directory above the one where the repo will be cloned.",
    )
    compile_parser.add_argument(
        "project_aliases", help="One or more project aliases to be parsed.", nargs="+"
    )

    args = parser.parse_args(sys.argv[1:])

    if "compile_destination" in args:
        for alias in args.project_aliases:
            projects[alias].install(args.compile_destination)
    else:
        display_alias_options()
