"""Step 80a analysis: are the real per-site phases beta*delta mod 2pi uniform, and does the empirical
defect-gas rate r(beta) = mean_s ln|1 + sum_j e^{i beta delta_{s,j}}| track the Mahler measure m(1+x_1+..+x_K)?"""
import numpy as np, math
D = np.load("shifts.npy", allow_pickle=True).item()
kinds = ["twin", "jag", "mutate", "cut"]
# Mahler measures via inner Jensen: m(1+x1+..+xK) = E log+|1 + x2 + .. + xK|  (K-1 uniform phases)
def mahler(K, n=600):
    if K == 1: return 0.0
    g = 2 * np.pi * (np.arange(n) + 0.5) / n; z = np.exp(1j * g)
    if K == 2: return float(np.mean(np.log(np.maximum(1, np.abs(1 + z)))))
    if K == 3:
        W = 1 + z[:, None] + z[None, :]; return float(np.mean(np.log(np.maximum(1, np.abs(W)))))
    tot = 0.0
    for a in z:  # K = 4
        W = 1 + a + z[:, None] + z[None, :]; tot += np.mean(np.log(np.maximum(1, np.abs(W))))
    return float(tot / n)
M = {K: mahler(K) for K in [1, 2, 3, 4]}
print("Mahler m(1+x1+..+xK):", {K: round(v, 4) for K, v in M.items()}, " check K=3 vs 7zeta(3)/(2pi^2) =", round(7 * 1.2020569 / (2 * np.pi ** 2), 4))
sets = {1: ["twin"], 2: ["twin", "cut"], 4: kinds}
res = {}
for d in [2, 4]:
    for e in [1.0, 0.1]:
        per = (math.pi if d == 2 else 2 * math.pi * math.sqrt(6) / 4) if e == 1 else None
        betas = np.linspace(0.02, per - 0.02, 400) if per else np.geomspace(0.1, 300, 400)
        dd = {k: D[d][(e, k)] for k in kinds}
        ok = np.all([~np.isnan(dd[k]) for k in kinds], axis=0)
        dd = {k: v[ok] for k, v in dd.items()}; Ns = ok.sum()
        R1 = {k: np.abs(np.exp(1j * np.outer(betas, dd[k])).mean(1)) for k in kinds}
        line = f"\nd={d} eps={e} sites={Ns} beta in [{betas[0]:.2f},{betas[-1]:.2f}]" + (f" (period {per:.3f})" if per else "")
        print(line)
        for K, ks in sets.items():
            W = 1 + sum(np.exp(1j * np.outer(betas, dd[k])) for k in ks)
            r = np.log(np.abs(W)).mean(1)
            # 'generic' beta: all involved kinds have Rayleigh < 3/sqrt(N)
            gen = np.all([R1[k] < 3 / math.sqrt(Ns) for k in ks], axis=0)
            res[(d, e, K)] = (betas, r, gen)
            print(f"  K={K}: Mahler {M[K]:.3f} | generic-beta fraction {gen.mean():.2f}, rate there mean {r[gen].mean() if gen.any() else float('nan'):+.3f} "
                  f"(sd {r[gen].std() if gen.any() else float('nan'):.3f}) | overall min {r.min():+.3f} max {r.max():.3f} | fraction beta with r<0: {(r<0).mean():.3f}")
        print("  Rayleigh |<e^{i beta delta}>| median over beta: " + ", ".join(f"{k} {np.median(R1[k]):.3f}" for k in kinds) + f"  (uniform ~ {1/math.sqrt(Ns):.3f})")
np.save("uniform_res.npy", {"M": M, "res": res}, allow_pickle=True)
