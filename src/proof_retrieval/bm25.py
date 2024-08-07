from typing import Optional
import functools
import math
from data_management.dataset_file import get_ids_from_goal, get_ids_from_sentence


def doc_to_hashable(doc: list[str]) -> str:
    return "<DOCSEP>".join(doc)


def doc_from_hashable(s: str) -> list[str]:
    return s.split("<DOCSEP>")


@functools.lru_cache(10000)
def bm_compute_term_freqs(doc_str: str) -> dict[str, int]:
    doc = doc_from_hashable(doc_str)
    return compute_term_freqs(doc)


def compute_term_freqs(doc: list[str]) -> dict[str, int]:
    term_freqs: dict[str, int] = {}
    for term in doc:
        if term not in term_freqs:
            term_freqs[term] = 0
        term_freqs[term] += 1
    return term_freqs


def compute_doc_freqs(corpus: list[list[str]]) -> dict[str, int]:
    doc_freqs: dict[str, int] = {}
    for doc in corpus:
        for word in set(doc):
            if word not in doc_freqs:
                doc_freqs[word] = 0
            doc_freqs[word] += 1
    return doc_freqs


def bm25(
    query: list[str],
    docs: list[list[str]],
    k1: float = 1.8,
    b: float = 0.75,
    doc_freqs: Optional[dict[str, int]] = None,
) -> list[float]:
    if 0 == len(docs):
        return []
    avg_doc_len = sum([len(d) for d in docs]) / len(docs)
    if doc_freqs is None:
        doc_freqs = compute_doc_freqs(docs)
    doc_term_freqs = [bm_compute_term_freqs(doc_to_hashable(d)) for d in docs]

    similarities: list[float] = []
    for doc, doc_term_dict in zip(docs, doc_term_freqs):
        doc_similarity = 0
        for term in query:
            if term not in doc_freqs:
                continue
            if term not in doc_term_dict:
                continue
            query_idf = math.log(
                (len(docs) - doc_freqs[term] + 0.5) / (doc_freqs[term] + 0.5) + 1
            )
            doc_term_num = doc_term_dict[term] * (k1 + 1)
            doc_term_denom = doc_term_dict[term] + k1 * (
                1 - b + b * len(doc) / avg_doc_len
            )
            doc_similarity += query_idf * doc_term_num / doc_term_denom
        similarities.append(doc_similarity)
    return similarities
