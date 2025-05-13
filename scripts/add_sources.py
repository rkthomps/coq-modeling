"""
Sometimes opam install doesn't gather the source files.
This takes a directory of source files and adds them to the opam switch directory.
"""

import shutil
import argparse
from pathlib import Path


def copy_source_files(source_dir: Path, opam_switch_dir: Path, dry=False):
    for f in opam_switch_dir.glob("**/*.vo"):
        vo_rel_path = f.relative_to(opam_switch_dir)
        v_rel_path = vo_rel_path.with_suffix(".v")
        vp_rel_path = vo_rel_path.with_suffix(".vp")
        vy_rel_path = vo_rel_path.with_suffix(".vy")
        source_v_path = source_dir / v_rel_path
        source_vp_path = source_dir / vp_rel_path
        source_vy_path = source_dir / vy_rel_path
        if source_v_path.exists():
            source_path = source_v_path
            source_rel_path = v_rel_path
        elif source_vp_path.exists():
            source_path = source_vp_path
            source_rel_path = vp_rel_path
        elif source_vy_path.exists():
            source_path = source_vy_path
            source_rel_path = vy_rel_path
        else:
            raise ValueError(
                f"Neither {source_v_path} nor {source_vp_path} nor {source_vy_path} exist. ")
        if dry:
            continue
        shutil.copy(source_path, opam_switch_dir / source_rel_path.with_suffix(".v"))
        


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--source_dir",
        type=str,
        required=True,
        help="Directory containing the source files to add.",
    )
    parser.add_argument(
        "--opam_switch_dir",
        type=str,
        required=True,
        help="Path to the opam switch directory.",
    )
    args = parser.parse_args()
    source_dir = Path(args.source_dir)
    opam_switch_dir = Path(args.opam_switch_dir)
    assert source_dir.exists(), f"Source directory {source_dir} does not exist."
    assert opam_switch_dir.exists(), f"Opam switch directory {opam_switch_dir} does not exist."
    copy_source_files(source_dir, opam_switch_dir, dry=True)
    copy_source_files(source_dir, opam_switch_dir)

    