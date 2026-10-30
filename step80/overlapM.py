"""Step 80b: exact defect-gas sums for larger M (K=1 twins: M<=16; K=2 twin/cut: M<=12), dilute vs dense,
three backgrounds.  Rate r_M(beta) = M^-1 ln|sum_conf e^{i beta (S_conf - S_clean)}|  vs product formula."""
import sys, itertools, numpy as np, multiprocessing as mp, pickle
sys.path.insert(0, "/home/claude/step77")
from smear import S2 as S2eps

def diamond(N, rng):
    X = []
    while len(X) < N:
        t, x = rng.random(), rng.random() - 0.5
        if abs(x) < t and abs(x) < 1 - t: X.append((t, x))
    X = np.array(X); R = (X[None, :, 0] - X[:, None, 0]) > np.abs(X[None, :, 1] - X[:, None, 1]); return X, R
def links_of(R):
    Rf = R.astype(np.float32); return R & ~((Rf @ Rf) > 0)
def act(R):
    Rf = R.astype(np.float32); H = np.bincount((Rf @ Rf)[R].astype(int), minlength=len(R) + 2)[None, :]
    return float(S2eps(H, len(R), 1.0)[0])
def build(R, sites, choice, cutlink):
    R = R.copy()
    for s, j in zip(sites, choice):
        if j == 2: a, b = cutlink[s]; R[a, b] = False
    tw = [s for s, j in zip(sites, choice) if j == 1]
    if not tw: return R
    m = len(R); k = len(tw); R2 = np.zeros((m + k, m + k), bool); R2[:m, :m] = R
    for i, s in enumerate(tw):
        R2[:m, m + i] = R[:, s]; R2[m + i, :m] = R[s]
        for i2, s2 in enumerate(tw): R2[m + i, m + i2] = R[s, s2]
    return R2

N = 200; BETAS = np.linspace(0.01, np.pi - 0.01, 300)
def setup(seed):
    rng = np.random.default_rng(seed); X, B = diamond(N, rng); LB = links_of(B)
    def cut_of(c):
        f = np.where(LB[c])[0]; p = np.where(LB[:, c])[0]
        return (c, int(f[0])) if len(f) else (int(p[0]), c)
    # interior candidates: away from the diamond boundary
    t, x = X[:, 0], X[:, 1]; margin = np.minimum(t - abs(x), 1 - t - abs(x))
    cand = np.where(margin > 0.08)[0]
    # farthest-point order for dilute sets
    order = [int(cand[np.argmin(((X[cand] - [0.5, 0]) ** 2).sum(1))])]
    while len(order) < 16:
        d = np.min(((X[cand][:, None] - X[order][None]) ** 2).sum(2), 1); order.append(int(cand[np.argmax(d)]))
    dense = list(np.argsort(((X - [0.5, 0]) ** 2).sum(1))[:16])
    return B, cut_of, order, dense

def job(args):
    seed, label, K, M = args
    B, cut_of, order, dense = setup(seed)
    sites = (order if label == "dilute" else dense)[:M]
    cl = {c: cut_of(c) for c in sites if True}
    opts = [0, 1] if K == 1 else [0, 1, 2]
    S = {}
    for ch in itertools.product(opts, repeat=M): S[ch] = act(build(B, sites, ch, cl))
    clean = S[(0,) * M]
    d = {(i, j): S[tuple(j if t == i else 0 for t in range(M))] - clean for i in range(M) for j in opts}
    Sv = np.array(list(S.values())) - clean
    ex = np.empty(len(BETAS))
    for a in range(0, len(BETAS), 20):
        ex[a:a + 20] = np.log(np.abs(np.exp(1j * np.outer(BETAS[a:a + 20], Sv)).sum(1)))
    pr = sum(np.log(np.abs(sum(np.exp(1j * BETAS * d[(i, j)]) for j in opts))) for i in range(M))
    return args, ex / M, pr / M

if __name__ == "__main__":
    jobs = []
    for seed in [1, 2, 3]:
        for label in ["dilute", "dense"]:
            for M in [4, 6, 8, 10, 12, 14, 16]: jobs.append((seed, label, 1, M))
            for M in [4, 6, 8, 10, 12]: jobs.append((seed, label, 2, M))
    jobs.sort(key=lambda a: -(a[2] + 1) ** a[3])
    out = {}
    with mp.Pool(2) as pool:
        for args, ex, pr in pool.imap_unordered(job, jobs):
            out[args] = (ex, pr); print(args, f"exact {ex.mean():+.3f} product {pr.mean():+.3f}", flush=True)
            pickle.dump(out, open("overlapM.pkl", "wb"))
