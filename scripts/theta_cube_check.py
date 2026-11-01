"""Finite check behind the numerical axiom `theta_cube_small` (Prelim/LambdaMu.lean):

  |theta(n) - n| < n / log^3 n      for 89 967 803 <= n <= 10^10

(the range of Dusart's bound [Dus18, Thm 4.2] below 10^10).  Segmented sieve up to 10^10 as in
`psi_mid_check.py` (segments of 5*10^6, < 1 GB RAM).  Reports the maximum of
|theta(n) - n| * log^3(n) / n over the range.  Rounding: theta is a cumulative float64 sum
(absolute error < 10^-1 within a segment, < 10^-5 across segments via math.fsum), negligible
against the margin.

Usage: python3 scripts/theta_cube_check.py   (a few minutes)
"""
import math
import numpy as np

LO = 89967803
LIMIT = 10 ** 10
SEG = 5 * 10 ** 6
r = math.isqrt(LIMIT) + 1
small = np.ones(r + 1, dtype=bool); small[:2] = False
for p in range(2, math.isqrt(r) + 1):
    if small[p]:
        small[p * p::p] = False
sp = [int(p) for p in np.nonzero(small)[0]]

theta = 0.0
best = (0.0, None)
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
    cth = theta + np.cumsum(th)
    theta = math.fsum([theta, math.fsum(th)])
    if end <= LO:
        continue
    n = np.arange(start, end, dtype=np.float64)
    m = n >= LO
    v = np.abs(cth[m] - n[m]) * np.log(n[m]) ** 3 / n[m]
    i = int(v.argmax())
    if v[i] > best[0]:
        best = (float(v[i]), int(n[m][i]))
print(f"max |theta(n)-n| log^3 n / n on [{LO}, 1e10] = {best[0]:.6f} at n = {best[1]}")
