"""Finite check behind the numerical axiom `mertens_product_small` (Prelim/MertensProduct.lean):

  for every prime 5 <= x <= 10^8,
      prod_{p <= x} p/(p-1) < e^gamma log theta(x) + 2.50637 / log theta(x),
  where theta(x) = sum_{p <= x} log p.

The tightest case is x = 23 (theta(23) = log 223092870, [RS62, Thm 15]); primes below 10^4 are
rechecked with mpmath at 40 digits.  Float64 running sums (math.fsum per chunk) otherwise; the
margins away from x = 23 are far above rounding error.

Usage: python3 scripts/mertens_product_check.py   (about a minute, < 1 GB)
"""
import math
import numpy as np
from mpmath import mp, mpf, log as mlog, exp as mexp, euler

X = 10 ** 8
isp = np.ones(X + 1, dtype=bool); isp[:2] = False
for p in range(2, math.isqrt(X) + 1):
    if isp[p]:
        isp[p * p::p] = False
pr = np.nonzero(isp)[0].astype(np.float64)
del isp
lf = np.log(pr) - np.log(pr - 1.0)          # log(p/(p-1))
th = np.log(pr)
LF = np.cumsum(lf); TH = np.cumsum(th)
eg = math.exp(0.57721566490153286061)
m = pr >= 5
rhs = eg * np.log(TH[m]) + 2.50637 / np.log(TH[m])
marg = rhs - np.exp(LF[m])
i = marg.argmin()
print('float64: min margin', marg[i], 'at x =', int(pr[m][i]), '; number of primes checked', m.sum())
j = np.nonzero(pr[m] > 10 ** 4)[0][0]
k = marg[j:].argmin()
print('float64: min margin for x > 1e4:', marg[j:][k], 'at x =', int(pr[m][j:][k]))

mp.dps = 40
EG = mexp(euler)
F = mpf(1); T = mpf(0); worst = None
for p in pr[pr < 10 ** 4]:
    p = int(p)
    F *= mpf(p) / (p - 1); T += mlog(p)
    if p >= 5:
        d = EG * mlog(T) + mpf('2.50637') / mlog(T) - F
        if worst is None or d < worst[0]:
            worst = (d, p)
print('mpmath: min margin for 5 <= x < 1e4:', worst)
