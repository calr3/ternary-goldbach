"""Finite checks behind the numerical axioms of Prelim/LambdaMuReduce.lean.

* psi_small:      psi(n) < 1.03883 n            for 1 <= n < 2*10^6
* nonprime_small: psi(n) - theta(n) < 1.4262 sqrt(n)   for 1 <= n <= 10^12
                  (psi - theta only jumps at prime powers p^k, k >= 2, p <= 10^6; we check the value
                  at every jump, where it is largest relative to sqrt(n))
* mertens_small:  sum_{m <= n} Lambda(m)/m <= log n   for 1 <= n <= 100

Usage: python3 scripts/psi_checks.py   (needs numpy, mpmath; a few seconds, < 200 MB)
"""
import math
import numpy as np
from mpmath import mp, mpf, log

N = 2_000_000
isp = np.ones(N + 1, dtype=bool); isp[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if isp[p]:
        isp[p * p::p] = False
primes = np.nonzero(isp)[0]
lam = np.zeros(N + 1)
for p in primes:
    pk = int(p)
    while pk <= N:
        lam[pk] = math.log(p); pk *= p
psi = np.cumsum(lam)
n = np.arange(N + 1, dtype=np.float64)
ratio = psi[1:N] / n[1:N]
print('psi_small: max psi(n)/n for n < 2e6 =', ratio.max(), 'at n =', 1 + ratio.argmax(),
      ' margin', 1.03883 - ratio.max())

# psi - theta at prime powers up to 1e12
Y = 10 ** 12
pts = []
for p in primes[primes <= 10 ** 6]:
    p = int(p); pk = p * p
    while pk <= Y:
        pts.append((pk, math.log(p))); pk *= p
pts.sort()
s = 0.0; worst = 0.0; at = None
for (v, l) in pts:
    s += l
    r = s / math.sqrt(v)
    if r > worst: worst, at = r, v
print('nonprime_small: max (psi-theta)(n)/sqrt(n) for n <= 1e12 =', worst, 'at n =', at,
      ' margin', 1.4262 - worst)

mp.dps = 30
worst = mpf(-10); S = mpf(0)
for m in range(1, 101):
    if lam[m] > 0:
        p = [int(q) for q in primes if m % q == 0][0]
        S += log(p) / m
    d = S - log(m)
    worst = max(worst, d)
print('mertens_small: max sum_{m<=n} Lambda(m)/m - log n for n <= 100 =', worst)
