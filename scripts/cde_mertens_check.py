"""Float check of the hypothesis `CDEMertens`: |M(n)| <= n/4345 for 2 160 535 <= n <= N,
M(n) = sum_{k<=n} mu(k) (mu by a sieve with the primes <= sqrt N).

Usage: python3 scripts/cde_mertens_check.py [N]   (default N = 10^8)"""
import sys, math
import numpy as np
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**8
mu = np.ones(N + 1, dtype=np.int8)
prod = np.ones(N + 1, dtype=np.int64)
r = math.isqrt(N)
isp = np.ones(r + 1, dtype=bool); isp[:2] = False
for p in range(2, math.isqrt(r) + 1):
    if isp[p]: isp[p * p::p] = False
for p in np.nonzero(isp)[0]:
    p = int(p)
    mu[::p] *= -1
    prod[::p] *= p
    mu[::p * p] = 0
idx = np.arange(N + 1, dtype=np.int64)
big = (prod != idx) & (mu != 0)
mu[big] *= -1
mu[0] = 0
M = np.cumsum(mu, dtype=np.int64)
lo = 2160535
ratio = np.abs(M[lo:]) * 4345 / idx[lo:]
k = int(np.argmax(ratio))
print(f"max 4345 |M(n)|/n over [{lo}, {N}] = {ratio[k]:.4f} at n = {lo + k} (M = {M[lo + k]})")
print("M(199) =", M[199], "; max |M(n)|/sqrt(n) over [100, 2160534] =",
      float(np.max(np.abs(M[100:lo]) / np.sqrt(idx[100:lo]))))
