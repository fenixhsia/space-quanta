import pickle, numpy as np, collections
D = pickle.load(open("overlapM.pkl", "rb"))
agg = collections.defaultdict(list)
for (seed, label, K, M), (ex, pr) in D.items():
    agg[(label, K, M)].append((ex.mean(), pr.mean(), np.mean(ex >= pr - 1e-9), ex.min(), np.mean(ex < 0)))
rows = []
for key in sorted(agg, key=lambda k: (k[1], k[0], k[2])):
    a = np.array(agg[key]); n = len(a)
    rows.append((key, n, a[:, 0].mean(), a[:, 0].std(ddof=1) / np.sqrt(n) if n > 1 else np.nan, a[:, 1].mean(), a[:, 2].mean(), a[:, 4].mean()))
    print(f"{key[0]:6s} K={key[1]} M={key[2]:2d} n={n}: exact {a[:,0].mean():+.3f}±{(a[:,0].std(ddof=1)/np.sqrt(n) if n>1 else 0):.3f}  product {a[:,1].mean():+.3f}  frac(beta: exact>=product) {a[:,2].mean():.2f}  frac(exact<0) {a[:,4].mean():.3f}")
pickle.dump(rows, open("anaM.pkl", "wb"))
