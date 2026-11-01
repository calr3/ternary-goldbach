"""Finite checks behind the numerical axioms `psi_mid`, `psi_sqrt`, `theta_sqrt`, `psi_mul_mid`
(Prelim/LambdaMu.lean).  Segmented sieve up to 10^10 (segments of 5*10^6, < 1 GB RAM).

  psi_mid      psi(n) <= 1.0004 n                       for 2*10^6 <= n <= 10^9
  psi_sqrt     |psi(n) - n| <= c sqrt(n)               for 11 <= n <= 10^10
  theta_sqrt   |theta(n) - n| <= c' sqrt(n)            for 5*10^5 <= n <= 10^10
  psi_mul_mid  sum_{m<=n} Lambda(m) m < 1.0008 n^2/2   for 1.6*10^6 <= n <= 10^8

Rounding: within a segment psi and theta are cumulative float64 sums of < 10^7 terms of size
< 25 (absolute error < 10^-1); across segments the running totals are carried with math.fsum
(error < 10^-5 in total).  The sum of Lambda(m) m is carried in long double.  All reported
margins exceed these errors by orders of magnitude.

Usage: python3 scripts/psi_mid_check.py   (a few minutes)

NOTE (2026-11-01): the corresponding axioms are no longer used; they are proved from Büthe's
bounds (`buthe_theta`, `buthe_psi`) and kernel-checked computations (see AXIOMS.md, "Removed axioms").
This script is kept for reference.
"""
import bisect
import math
import numpy as np

LIMIT = 10 ** 10
SEG = 5 * 10 ** 6
r = math.isqrt(LIMIT) + 1
small = np.ones(r + 1, dtype=bool); small[:2] = False
for p in range(2, math.isqrt(r) + 1):
    if small[p]:
        small[p * p::p] = False
sp = [int(p) for p in np.nonzero(small)[0]]
ppw = []
for p in sp:
    v = p * p
    while v <= LIMIT:
        ppw.append((v, math.log(p))); v *= p
ppw.sort()
ppv = [v for v, _ in ppw]

psi = 0.0; theta = 0.0
S = np.longdouble(0)
st = dict(psi_mid=(0.0, None), psi_up=(0.0, None), psi_lo=(0.0, None),
          th_up=(0.0, None), th_lo=(0.0, None), mul=(1e9, None))
def upd(key, arr, nn, mode):
    if arr.size == 0:
        return
    i = arr.argmax() if mode == 'max' else arr.argmin()
    v = float(arr[i]); cur = st[key][0]
    if (mode == 'max' and v > cur) or (mode == 'min' and v < cur):
        st[key] = (v, int(nn[i]))

for start in range(0, LIMIT + 1, SEG):
    end = min(start + SEG, LIMIT + 1)
    seg = np.ones(end - start, dtype=bool)
    if start == 0:
        seg[:2] = False
    for p in sp:
        if p * p >= end:
            break
        first = max(p * p, ((start + p - 1) // p) * p)
        seg[first - start::p] = False
    idx = np.nonzero(seg)[0]
    th = np.zeros(end - start)
    th[idx] = np.log((idx + start).astype(np.float64))
    lam = th.copy()
    a = bisect.bisect_left(ppv, start); b = bisect.bisect_left(ppv, end)
    for v, l in ppw[a:b]:
        lam[v - start] += l
    cpsi = psi + np.cumsum(lam); cth = theta + np.cumsum(th)
    psi = math.fsum([psi, math.fsum(lam)]); theta = math.fsum([theta, math.fsum(th)])
    n = np.arange(start, end, dtype=np.float64); sq = np.sqrt(n)
    m = (n >= 2e6) & (n <= 1e9)
    if m.any():
        upd('psi_mid', cpsi[m] / n[m], n[m], 'max')
    m = n >= 11
    upd('psi_up', (cpsi[m] - n[m]) / sq[m], n[m], 'max')
    upd('psi_lo', (n[m] - cpsi[m]) / sq[m], n[m], 'max')
    m = n >= 5e5
    if m.any():
        upd('th_up', (cth[m] - n[m]) / sq[m], n[m], 'max')
        upd('th_lo', (n[m] - cth[m]) / sq[m], n[m], 'max')
    if start <= 10 ** 8:
        nl = np.arange(start, end, dtype=np.longdouble)
        cS = S + np.cumsum(lam.astype(np.longdouble) * nl)
        S = cS[-1]
        m = (n >= 1.6e6) & (n <= 1e8)
        if m.any():
            upd('mul', ((np.longdouble(1.0008) * nl[m] ** 2 / 2 - cS[m]) / nl[m] ** 2).astype(np.float64),
                n[m], 'min')

print('psi_mid   : max psi(n)/n on [2e6,1e9]           =', st['psi_mid'])
print('psi_sqrt  : max (psi(n)-n)/sqrt n on [11,1e10]   =', st['psi_up'])
print('            max (n-psi(n))/sqrt n on [11,1e10]   =', st['psi_lo'])
print('theta_sqrt: max (theta(n)-n)/sqrt n on [5e5,1e10] =', st['th_up'])
print('            max (n-theta(n))/sqrt n on [5e5,1e10] =', st['th_lo'])
print('psi_mul_mid: min (1.0008 n^2/2 - S(n))/n^2 on [1.6e6,1e8] =', st['mul'])
