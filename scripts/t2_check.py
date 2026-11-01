"""Independent float64 check of `T2_le` ([B, (5.31)], MinorArcs/TypeIIS1.lean) on the range that [B]
covers by computation, 16 <= S <= 10^5:

    T2(S) = sum_{s <= S odd} (1/s) int_{1/2}^1 g2(uS/s) du <= 0.37273,

g2(x) = sum_{r1, r2 <= x, (r1, r2) = 1, r1 r2 odd} mu(r1) mu(r2)/(sigma(r1) sigma(r2)).
(For S >= 10^5, [B] derives (5.31) analytically from Lemma 5.1.2 and (5.30).)

g2 is a step function, computed at every integer n <= 10^5 from
g2(n) = sum_d mu(d) (sum_{r <= n, d | r} f(r))^2,  f(r) = mu(r)/sigma(r) for odd r.
Then int_0^y g2 is piecewise linear, and T2(S) = (1/S) sum_{s odd <= S} [G(S/s) - G(S/2s)].
T2 is evaluated on a grid: step 1/64 on [16, 2000], then 200000 log-spaced points up to 10^5.
This is a plausibility check (float64, a grid, not interval arithmetic).

Usage: python3 scripts/t2_check.py   (a few minutes; needs numpy, sympy)
"""
import math
import numpy as np
from sympy import factorint

N = 10 ** 5
f = np.zeros(N + 1)
divs = [None] * (N + 1)
for r in range(1, N + 1, 2):
    fa = factorint(r)
    if any(e > 1 for e in fa.values()):
        continue
    ps = list(fa)
    sigma = 1
    for p in ps:
        sigma *= p + 1
    f[r] = (-1) ** len(ps) / sigma
    ds = [(1, 1)]
    for p in ps:
        ds += [(d * p, -m) for d, m in ds]
    divs[r] = ds
S_d = np.zeros(N + 1)
g2 = np.zeros(N + 1)
cur = 0.0
for n in range(1, N + 1):
    if f[n] != 0:
        fn = f[n]
        for d, m in divs[n]:
            cur += m * (2 * S_d[d] * fn + fn * fn)
            S_d[d] += fn
    g2[n] = cur
cum = np.concatenate([[0.0], np.cumsum(g2)])        # cum[k] = int_0^k g2

def G(y):
    k = np.floor(y).astype(np.int64)
    return cum[k] + (y - k) * g2[k]

def T2(S):
    s = np.arange(1, math.floor(S) + 1, 2, dtype=np.float64)
    return float(np.sum(G(S / s) - G(S / (2 * s)))) / S

grid = np.concatenate([np.arange(16, 2000, 1 / 64), np.geomspace(2000, N, 200000)])
worst = (0.0, None)
for S in grid:
    v = T2(S)
    if v > worst[0]:
        worst = (v, S)
print("g2(1..8) =", g2[1:9])
print("max T2 on the grid in [16, 1e5]: %.6f at S = %.4f  (need <= 0.37273)" % worst)
assert worst[0] <= 0.37273
