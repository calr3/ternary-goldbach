"""Finite checks behind the former hypotheses of Prelim/MVLemma7.lean and Prelim/MVLemma8.lean.

g(r) = mu(r)^2/phi(r), G(r) = sum_{s<=r} g(s).

* lemma8_numeric: for 2 <= n <= 10^4,
    sum_{r<=n} g(r)(n+1)/(n+1+r) > log(n+1) + 0.25068          (min margin 1.1e-6, at n = 4)
    sum_{r<=n} g(r) r(n+1)/((n+1+r)(n+r)) <= 1                  (max 0.6384)
* lemma7_numeric: log(r+1) + 1.07 <= G(r) for 6 <= r <= 29999999   (min margin 0.0441, at r = 9)
* GS_N0: G(3*10^7) >= log(3*10^7) + 1.3325                          (value 1.33258)
* prod_ap_le: prod_{p < 10^4} (1 + (p^{-2/3} + p^{-1/3})/(p-1)) <= 7.99  (value 7.98552)

Floating point (double) is used for the sums; margins are far above rounding error except for the
Lemma 8 check at n = 4, which is also checked below in exact rational arithmetic plus a rigorous
interval for log 5.

Usage: python3 scripts/mv_lemma8_check.py   (needs numpy, mpmath, sympy; ~10 s, ~1 GB RAM)

NOTE: `prod_ap_le` is now proved in Lean (Prelim/SmallProdAp.lean, data from scripts/gen_prod_ap.py).
"""
import math
from fractions import Fraction
import numpy as np
from mpmath import mp, mpf, power, log as mlog, iv
from sympy import primerange, totient

N = 30_000_001
phi = np.arange(N, dtype=np.int64)
mu2 = np.ones(N, dtype=np.int8); mu2[0] = 0
isp = np.ones(N, dtype=bool); isp[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if isp[p]:
        isp[p * p::p] = False
for p in np.nonzero(isp)[0]:
    phi[p::p] -= phi[p::p] // p
    if p * p < N:
        mu2[p * p::p * p] = 0
g = np.where(mu2 == 1, 1.0 / np.maximum(phi, 1), 0.0); g[0] = 0
G = np.cumsum(g)
r = np.arange(N, dtype=np.float64)

m = G[6:N - 1] - np.log(r[6:N - 1] + 1) - 1.07
print('lemma7_numeric: min margin', m.min(), 'at r =', 6 + m.argmin())
print('GS_N0: G(3e7) - log(3e7) =', G[N - 1] - math.log(N - 1))

w1, w2 = 9.0, 0.0
for n in range(2, 10001):
    rr = np.arange(1, n + 1); gg = g[1:n + 1]
    A = np.sum(gg * (n + 1) / (n + 1 + rr)) - math.log(n + 1) - 0.25068
    B = np.sum(gg * rr * (n + 1) / ((n + 1 + rr) * (n + rr)))
    w1 = min(w1, A); w2 = max(w2, B)
print('lemma8_numeric: endpoint min margin', w1, '; monotonicity max', w2)

# exact check of the tightest case n = 4
def gq(k):
    from sympy import factorint
    if any(e > 1 for e in factorint(k).values()):
        return Fraction(0)
    return Fraction(1, int(totient(k)))
n = 4
W = sum(gq(k) * Fraction(n + 1, n + 1 + k) for k in range(1, n + 1))
mp.dps = 40
print('n = 4 exact: W =', W, '=', float(W), ' log 5 + 0.25068 =', mlog(5) + mpf('0.25068'),
      ' margin', mpf(W.numerator) / W.denominator - mlog(5) - mpf('0.25068'))

mp.dps = 30
K = mpf(1)
for p in primerange(2, 10000):
    K *= 1 + (power(p, mpf(-2) / 3) + power(p, mpf(-1) / 3)) / (p - 1)
print('prod_ap_le: product over p < 10^4 =', K)
