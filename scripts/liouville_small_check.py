"""Float check of `liouville_small` (Prelim/LiouvilleBound.lean; kernel-checked in Prelim/SmallLiouville.lean):

    |l(k)| log(k+1) <= 0.99   for 1 <= k <= 10^5,   l(k) = sum_{n <= k} lambda(n)/n,

so |l(z)| log z <= 0.99 for real 1 < z < 10^5 + 1 (Ramare, Acta Arith. 165 (2014), Lemma 2.4: <= 0.55 for
all z > 1).  lambda(n) = (-1)^Omega(n) from a sieve over prime powers; the partial sums are exact rationals
(fractions.Fraction would be slow, so they are float64 with the maximum reported; the margin is large).
Usage: python3 scripts/liouville_small_check.py   (a second)
"""
import numpy as np, math
N = 10**5
om = np.zeros(N + 2, np.int64)
isp = np.ones(N + 2, bool); isp[:2] = False
for p in range(2, N + 2):
    if isp[p]:
        isp[2*p::p] = False
        pk = p
        while pk <= N + 1:
            om[pk::pk] += 1; pk *= p
lam = np.where(om % 2 == 0, 1.0, -1.0)
n = np.arange(N + 2, dtype=np.float64); n[0] = 1.0
l = np.cumsum(np.where(np.arange(N + 2) >= 1, lam / n, 0.0))
k = np.arange(1, N + 1)
v = np.abs(l[1:N + 1]) * np.log(k + 1.0)
i = int(np.argmax(v))
print("max_{1<=k<=1e5} |l(k)| log(k+1) =", v[i], "at k =", k[i])
print("l(1..6):", l[1:7])
