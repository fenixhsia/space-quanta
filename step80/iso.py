"""Step 80c: do distinct defect configurations give non-isomorphic posets?
Invariant: Weisfeiler-Lehman refinement on the order (colour <- (colour, multiset of past colours, multiset of
future colours)), multisets hashed by sums of random 64-bit weights; final graph invariant = sorted colour multiset.
Distinct invariants => non-isomorphic (rigorous in that direction).  Collisions are reported for exact checking."""
import sys, itertools, numpy as np, collections
sys.path.insert(0, "/home/claude/step80")
from overlapM import setup, build
rng0 = np.random.default_rng(12345); P = (1 << 61) - 1
def wl_invariant(R, iters=4):
    n = len(R); Ri = R.astype(np.int64)
    col = (R.sum(0) * 1000003 + R.sum(1)) % P             # (|past|, |future|)
    for _ in range(iters):
        _, idx = np.unique(col, return_inverse=True)
        w1 = rng_w1[idx]; w2 = rng_w2[idx]
        past = (Ri.T @ w1) % P if False else (R.T.astype(np.float64) @ w1f[idx])
        fut = R.astype(np.float64) @ w2f[idx]
        key = np.stack([idx, np.round(past * 1e6).astype(np.int64), np.round(fut * 1e6).astype(np.int64)], 1)
        _, col = np.unique(key, axis=0, return_inverse=True)
        # make colours canonical across graphs: hash of key
        col = np.array([hash(tuple(k)) for k in key], dtype=np.int64) % P
    return tuple(sorted(col.tolist()))
NC = 1 << 16
rng_w1 = rng0.integers(1, P, NC); rng_w2 = rng0.integers(1, P, NC)
w1f = rng0.random(NC); w2f = rng0.random(NC)

for seed in [1, 2]:
    B, cut_of, order, dense = setup(seed)
    for label, sites0 in [("dilute", order), ("dense", dense)]:
        M = 8; sites = sites0[:M]; cl = {c: cut_of(c) for c in sites}
        inv = {}
        for ch in itertools.product([0, 1, 2], repeat=M):
            inv[ch] = wl_invariant(build(B, sites, ch, cl))
        groups = collections.defaultdict(list)
        for ch, v in inv.items(): groups[v].append(ch)
        coll = [g for g in groups.values() if len(g) > 1]
        print(f"seed {seed} {label}: {len(inv)} configurations, {len(groups)} distinct invariants, collision groups {len(coll)}"
              + (f", e.g. {coll[:3]}" if coll else ""), flush=True)
