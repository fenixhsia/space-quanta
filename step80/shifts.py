"""Step 80a: single-defect action shifts on 2D and 4D sprinkled diamonds, every site, four defect kinds,
eps = 1 (BD) and eps = 0.1 (smeared).  Same defect poset is used for both eps."""
import sys, numpy as np
sys.path.insert(0, "/home/claude/step77"); sys.path.insert(0, "/home/claude/step78")
from smear import S2, S4
from clone2 import sprinkle, links_of
from trackB import defect

def hist(R):
    Rf = R.astype(np.float32); C = (Rf @ Rf)[R].astype(int)
    return np.bincount(C, minlength=len(R) + 2)[None, :]
kinds = ["twin", "jag", "mutate", "cut"]; EPS = [1.0, 0.1]
out = {}
for d, N in [(2, 300), (4, 300)]:
    rng = np.random.default_rng(80 + d)
    B = sprinkle(N, d, rng); LB = links_of(B)
    S = S2 if d == 2 else S4
    H0 = hist(B); S0 = {e: float(S(H0, N, e)[0]) for e in EPS}
    D = {(e, k): np.full(N, np.nan) for e in EPS for k in kinds}
    for c in range(N):
        for k in kinds:
            R2 = defect(B, LB, c, k, rng)
            if R2 is None: continue
            H = hist(R2)
            for e in EPS: D[(e, k)][c] = float(S(H, len(R2), e)[0]) - S0[e]
    out[d] = D
    for e in EPS:
        print(f"d={d} eps={e}: " + "  ".join(f"{k} sd {np.nanstd(D[(e,k)]):.3g} med|d| {np.nanmedian(np.abs(D[(e,k)])):.3g}" for k in kinds))
np.save("shifts.npy", out, allow_pickle=True)
