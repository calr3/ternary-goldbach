"""Finite check behind the former hypothesis `C_grid` (Prelim/LiouvilleBound.lean).

With beta(a, u) = min(5/3, 0.99/(a - 2 log u)) if 2 log u < a, else 5/3, and
    G(a) = sum_{u=1}^{3000} |mu(u)|/u^2 * beta(a, u) + (5/3)/(3000 + 1/2),
the former hypothesis stated  (2.8 + (i+1)/100) * G(2.8 + i/100) <= 2.8  for 0 <= i < 7720  (grid on [2.8, 80]).
This is the optimisation in Ramare, Acta Arith. 165 (2014), proof of Thm 1.1 (rho(U, y)), with our constants
0.99 (|l(z)| log z) and 5/3 (|l_q| <= sum 1/u^2), restricted to squarefree u.
Float64; the margin is about 0.06.   Usage: python3 scripts/moebius_C_grid.py   (seconds)
"""
import numpy as np
U0 = 3000
sf = np.ones(U0 + 1, bool); sf[0] = False
for p in range(2, int(U0 ** 0.5) + 1):
    sf[p*p::p*p] = False
u = np.arange(1, U0 + 1, dtype=float); w = sf[1:] / (u * u); tl = 2 * np.log(u)
tail = (5 / 3) / (U0 + 0.5)
def G(a):
    beta = np.where(tl < a, np.minimum(5 / 3, 0.99 / np.maximum(a - tl, 1e-300)), 5 / 3)
    return float(np.dot(w, beta)) + tail
worst = 0.0; at = None
for i in range(7720):
    v = (2.8 + (i + 1) / 100) * G(2.8 + i / 100)
    if v > worst: worst, at = v, i
print("max_i (2.8 + (i+1)/100) G(2.8 + i/100) =", worst, "at i =", at, " (need <= 2.8)")
