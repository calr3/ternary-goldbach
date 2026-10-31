"""Finite checks behind the numerical axioms for [B, (2.16)] and [B, (2.18)] (Prelim/LambdaMuExtra.lean).

* lambda_mul_small:  sum_{n<=k} Lambda(n) n <= 1.03884 k^2/2          for 663 <= k <= 1.6*10^6
* lambda_sqrt_small: sum_{n<=k} Lambda(n)/sqrt(n) < 2.0008 sqrt(k)     for 1 <= k <= 2*10^6
* lambda_sqrt_point: sum_{n<=K} Lambda(n)/sqrt(n) - psi(K)/sqrt(K+1) - 1.0004 sqrt(K+1) <= -2,  K = 2*10^6
Float64 with the margins reported.   Usage: python3 scripts/psi_extra_check.py   (seconds)
"""
import numpy as np, math
N = 2_000_001
isp = np.ones(N + 1, bool); isp[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if isp[p]: isp[p*p::p] = False
lam = np.zeros(N + 1)
for p in np.nonzero(isp)[0]:
    p = int(p); pk = p
    while pk <= N:
        lam[pk] = math.log(p); pk *= p
n = np.arange(N + 1, dtype=float)
A = np.cumsum(lam * n)
k = np.arange(663, 1600001)
r = A[k] / (k * k / 2.0)
print("lambda_mul_small: max ratio", r.max(), "at k =", k[r.argmax()], " (need <= 1.03884)")
B = np.cumsum(np.where(n > 0, lam / np.sqrt(np.maximum(n, 1)), 0.0))
k = np.arange(1, 2000001)
r = B[k] / np.sqrt(k)
print("lambda_sqrt_small: max ratio", r.max(), "at k =", k[r.argmax()], " (need < 2.0008)")
K = 2_000_000
psi = np.cumsum(lam)
v = B[K] - psi[K] / math.sqrt(K + 1) - 1.0004 * math.sqrt(K + 1)
print("lambda_sqrt_point: value", v, " (need <= -2)")
