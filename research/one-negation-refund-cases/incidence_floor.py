"""Smallest incidence profiles left by the one-full-row bound."""
from math import comb


def least_pairs(vertices, total):
    degree, remainder = divmod(total, vertices)
    return vertices * comb(degree, 2) + remainder * degree


def candidates(v, k):
    for t in range(2, comb(v, 2) // comb(k + 2, 2) + 1):
        rest = max(t * (k + 1) + 1, (t - 1) * (k + 2))
        largest = (rest + t - 2) // (t - 1)
        total = rest + largest
        if least_pairs(t, total) <= comb(v, 2) and least_pairs(v, total) <= comb(t, 2):
            yield t, total


for k in range(3, 11):
    v = k + 2
    while not list(candidates(v, k)):
        v += 1
    print(f'k={k}: v>={v}, n>={v+k}, profiles={list(candidates(v,k))}')
