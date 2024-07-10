import functools
from pathlib import Path
from typing import Optional

import torch

from util.util import get_basic_logger

_logger = get_basic_logger(__name__)


@functools.lru_cache(1000)
def load_page(db_loc: Path, page_idx: int, device: str) -> Optional[torch.Tensor]:
    page_loc = get_page_loc(db_loc, page_idx)
    if not page_loc.exists():
        _logger.error(f"Page {page_idx} does not exist.")
        return None
    # return torch.load(page_loc).to("cuda")
    return torch.load(page_loc, map_location=device)


def group_idxs(idxs: list[int], page_size: int) -> dict[int, list[tuple[int, int]]]:
    page_idxs: dict[int, list[tuple[int, int]]] = {}
    for i, idx in enumerate(idxs):
        page_idx = idx // page_size
        if page_idx not in page_idxs:
            page_idxs[page_idx] = []
        page_idxs[page_idx].append((idx, i))  # vector idx, orig idx
    return page_idxs


def get_embs(
    idxs: list[int], page_size: int, db_loc: Path, device: str
) -> Optional[torch.Tensor]:
    page_groups = group_idxs(idxs, page_size)
    page_tensors: list[torch.Tensor] = []
    all_orig_idxs: list[int] = []
    for pg_num, pg_idxs in page_groups.items():
        page_idxs = [p for p, _ in pg_idxs]
        orig_idxs = [o for _, o in pg_idxs]
        all_orig_idxs.extend(orig_idxs)
        page_tensor = load_page(db_loc, pg_num, device)
        if page_tensor is None:
            _logger.error(f"No page for {pg_num} for indices {page_idxs}.")
            return None
        indices = torch.tensor(page_idxs, device=device) % page_size
        page_tensors.append((page_tensor[indices]))
    reidx = sorted(range(len(all_orig_idxs)), key=lambda idx: all_orig_idxs[idx])
    reidx_tensor = torch.tensor(reidx, device=device)
    big_tensor = torch.cat(page_tensors)
    return big_tensor[reidx_tensor]


def get(idx: int, page_size: int, db_loc: Path, device: str) -> Optional[torch.Tensor]:
    page = idx // page_size
    page_tensor = load_page(db_loc, page, device)
    if page_tensor is not None:
        return page_tensor[idx % page_size]
    return None


def get_page_loc(db_loc: Path, idx: int) -> Path:
    return db_loc / f"{idx}.pt"
