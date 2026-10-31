"""Finite checks behind numerical axioms of Prelim/LambdaMu.lean (small ranges).

* psi_small:      psi(n) < 1.03883 n            for 1 <= n < 2*10^6
* nonprime_small: psi(n) - theta(n) < 1.4262 sqrt(n)   for 1 <= n <= 10^12
                  (psi - theta only jumps at prime powers p^k, k >= 2, p <= 10^6; we check the value
                  at every jump, where it is largest relative to sqrt(n))
* mertens_small:  sum_{m <= n} Lambda(m)/m <= log n   for 1 <= n <= 100
* mertens_lower_small: sum_{m <= n} Lambda(m)/m >= log(n+1) - log(3/sqrt 2)  for 3 <= n <= 10^6
  (equality at n = 2, which is proved by hand)
* mertens_point:  sum_{m <= X} Lambda(m)/m - psi(X)/(X+1) - log(X+2) >= -1.5776, X = 10^6
* logsq_small:    sum_{n/2 < p <= n} (log p)^2 <= (1/2) n log n   for 117 <= n <= 10^6

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

# (2.13) small range, (2.19) small range (float64; margins reported)
X = 10 ** 6
A = np.cumsum(np.where(n[:X + 1] > 0, lam[:X + 1] / np.maximum(n[:X + 1], 1), 0.0))
k = np.arange(3, X + 1)
d = A[3:X + 1] - (np.log(k + 1.0) - math.log(3 / math.sqrt(2)))
print('mertens_lower_small: min margin for 3 <= n <= 1e6 =', d.min(), 'at n =', 3 + d.argmin())
print('mertens_point: value at X = 1e6:', A[X] - psi[X] / (X + 1) - math.log(X + 2))
th2 = np.cumsum(np.where(isp, np.log(np.maximum(n, 1)) ** 2, 0.0))
k = np.arange(117, X + 1)
d = 0.5 * k * np.log(k) - (th2[k] - th2[k // 2])
print('logsq_small: min margin for 117 <= n <= 1e6 =', d.min(), 'at n =', 117 + d.argmin())
