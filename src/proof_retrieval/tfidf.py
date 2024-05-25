from typing import Optional
import functools
import math


def clean_token(s: str) -> str:
    s = s.lstrip("(,:{")
    s = s.rstrip("),:}")
    return s


@functools.lru_cache(50000)
def tokenize(s: str) -> list[str]:
    whitespace_split = s.split()
    clean_tokens: list[str] = []
    for t in whitespace_split:
        clean_t = clean_token(t)
        if 0 < len(clean_t):
            clean_tokens.append(clean_t)
    return clean_tokens


def compute_idfs(corpus: list[list[str]]) -> dict[str, float]:
    if 0 == len(corpus):
        return {}
    assert 0 < len(corpus)
    doc_freqs: dict[str, int] = {}
    for doc in corpus:
        for word in set(doc):
            if word not in doc_freqs:
                doc_freqs[word] = 0
            doc_freqs[word] += 1

    idfs: dict[str, float] = {}
    for k, v in doc_freqs.items():
        idfs[k] = math.log(len(corpus) / v)
    return idfs


def doc_to_hashable(doc: list[str]) -> str:
    return "<DOCSEP>".join(doc)


def doc_from_hashable(s: str) -> list[str]:
    return s.split("<DOCSEP>")


@functools.lru_cache(10000)
def compute_doc_tf(doc_str: str) -> dict[str, float]:
    doc = doc_from_hashable(doc_str)
    # doc = tokenize(premise)
    if 0 == len(doc):
        return {}
    assert 0 < len(doc)
    term_freqs: dict[str, int] = {}
    for word in doc:
        if word not in term_freqs:
            term_freqs[word] = 0
        term_freqs[word] += 1

    tfs: dict[str, float] = {}
    for k, v in term_freqs.items():
        tfs[k] = v / len(doc)
    return tfs


def compute_query_tf(query: list[str]) -> dict[str, float]:
    if 0 == len(query):
        return {}
    assert 0 < len(query)
    term_freqs: dict[str, int] = {}
    max_term_freq = 0
    for word in query:
        if word not in term_freqs:
            term_freqs[word] = 0
        term_freqs[word] += 1
        if max_term_freq < term_freqs[word]:
            max_term_freq = term_freqs[word]

    tfs: dict[str, float] = {}
    for k, v in term_freqs.items():
        tfs[k] = 0.5 + 0.5 * (v / max_term_freq)
    return tfs


def tf_idf(
    query: list[str], docs: list[list[str]], idfs: Optional[dict[str, float]] = None
) -> list[float]:
    if idfs is None:
        idfs = compute_idfs(docs)
    query_tfs = compute_query_tf(query)
    doc_tfs = [compute_doc_tf(doc_to_hashable(d)) for d in docs]
    similarities: list[float] = []
    for doc_tf_dict in doc_tfs:
        dot_prod = 0
        for term, query_tf in query_tfs.items():
            if term not in doc_tf_dict:
                continue
            if term not in idfs:
                continue
            query_tf_idf = query_tf * idfs[term]
            doc_tf_idf = doc_tf_dict[term] * idfs[term]
            dot_prod += query_tf_idf * doc_tf_idf
        similarities.append(dot_prod)
    return similarities
