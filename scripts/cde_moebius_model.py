"""Float model: |m(x)| log x from Cohen-Dress-El Marraki's |M(x)| <= x/4345 (x >= 2 160 535), where
m(x) = sum_{n<=x} mu(n)/n and M(x) = sum_{n<=x} mu(n).

Identity (MoebiusDecay.mlog_identity with c = -gamma), E(y) = sum_{n<=y} Lambda(n)/n - log y + gamma:
    m(x) (log x - gamma) = - sum_{d<=x} mu(d)/d E(x/d).
Split at d = x/Y.
  A = sum_{d<=x/Y} |E(x/d)|/d                      (needs |E(y)| <= e(y) for y >= Y)
  B = the rest, by Abel summation against M:  with |M(t)| <= beta(t) t,
      B <= beta(x) gamma + beta(x/Y) |E(Y)| + sum_{k<=Y} beta(x/k) Lambda(k)/k
           + int_1^Y beta(x/u) |1 - E(u)| du/u,
      beta = 1/4345 from 2 160 535 (CDE) and 0.5671/sqrt t on [100, 2 160 535) (finite check).
E(y) = (psi(y) - y)/y - R(y), R(y) = int_y^oo (psi(u) - u)/u^2 du. Scenarios for e(y):
  lean:  the E bounds the development has: |E1(t) - E1(x)| <= Dvar(x) for t >= x >= 1e12
         (MertensProduct.E1_var), anchored at 1e12 below it, with |psi(y) - y| <= c(y) sqrt y.
  R:     an explicit formula for R: R(y) = sum_rho y^(rho-1)/(rho(1-rho)) + O(1/y), so with RH
         to 1e8 |R(y)| <= 0.047/sqrt y + 6e-8 (sum 1/|rho|^2 = 0.0462; zeros above 1e8: 6e-8).
  R+tab: R as above, and E(y) itself from a finite table for y < 1e6.
Above 1e17 add the plateau: psi's relative error 4.92e-7 adds about 4.92e-7 log x to |m(x)| log x.

Needed by the uses (g2_tail_moebius_model.py, liouville_222_model.py): about 0.073/log x for
x >= 11815; the float max of |m(k)| log(k+1) on [11815, 1e6] is 0.0295.

Usage: python3 scripts/cde_moebius_model.py   (a few seconds)"""
import math
import numpy as np

g = 0.5772156649015329
N = 10 ** 7
s = np.ones(N + 1, bool); s[:2] = False
for p in range(2, int(N ** .5) + 1):
    if s[p]: s[p * p::p] = False
P = np.nonzero(s)[0]
lam = np.zeros(N + 1); lam[P] = np.log(P)
for p in P[P * P <= N]:
    q = p * p
    while q <= N: lam[q] = math.log(p); q *= p
n = np.arange(N + 1, dtype=float); n[0] = 1
L = np.cumsum(lam / n)
eabs = np.maximum(abs(L[1:] - np.log(np.arange(2, N + 2)) + g), abs(L[1:] - np.log(np.arange(1, N + 1)) + g))

mu = np.ones(2_200_001, np.int8); mu[0] = 0
isp = np.ones(2_200_001, bool); isp[:2] = False
for p in range(2, 2_200_001):
    if isp[p]: isp[2 * p::p] = False; mu[p::p] *= -1; mu[p * p::p * p] = 0
M = np.cumsum(mu.astype(np.int64)); t = np.arange(len(M))
print("max |M(t)|/sqrt t on [100, 2160535]:", round(float((abs(M[100:2160536]) / np.sqrt(t[100:2160536])).max()), 4))
m = np.cumsum(mu[1:1_000_001] / np.arange(1, 1_000_001))
print("max |m(k)| log(k+1) on [11815, 1e6]:", round(float((abs(m[11814:]) * np.log(np.arange(11816, 1_000_002))).max()), 5))

ly = np.linspace(0, math.log(1e17), 170001); y = np.exp(ly); dl = ly[1] - ly[0]
c = np.select([y < 1e6, y < 5e7, y < 1e8, y < 3.2e10, y < 1e15], [1.0, 5.0, 33, 35.5, 72], 200)
I = np.cumsum((c * y ** -0.5 * dl)[::-1])[::-1]
i12 = np.searchsorted(ly, math.log(1e12))
D12 = 1443 / 1e6 + 13 / 1e12 + 16 / math.log(1e12) ** 3 + 8.5e-6
with np.errstate(divide="ignore"):
    e_lean = np.where(y < 1e12, D12 + c / np.sqrt(y) + 35.5 / 1e6 + np.maximum(I - I[i12], 0),
                      1443 / np.sqrt(y) + 16 / np.log(y) ** 3 + 8.5e-6)
e_R = (c + 0.047) / np.sqrt(y) + 6e-8
e_true = eabs[np.clip(y.astype(np.int64), 1, N) - 1]
beta = lambda t: np.where(t >= 2160535, 1 / 4345, np.where(t >= 100, 0.5671, np.where(t >= 10, 0.8321, 1.0)) / np.sqrt(t))

def B(x, Y):
    k = np.arange(1, int(Y) + 1)
    u = np.exp(np.linspace(0, math.log(Y), 4000))
    Eu = eabs[np.clip(u.astype(np.int64), 1, N) - 1]
    return (float(beta(np.array(x))) * g + float(beta(np.array(x / Y))) * eabs[int(Y) - 1]
            + (beta(x / k) * lam[1:int(Y) + 1] / k).sum() + (beta(x / u) * (1 + Eu)).sum() * math.log(Y) / 3999)

def A(e, x, Y):
    sel = (y >= Y) & (y <= x)
    return e[sel].sum() * dl + float(np.interp(math.log(x), ly, e))

for name, e in [("lean", e_lean), ("R", e_R), ("R+tab", np.where(y < 1e6, e_true, e_R))]:
    print(f"{name}:")
    for x in [1e5, 1e6, 1e7, 1e8, 1e10, 1e12, 1e17]:
        v, Y = min(((A(e, x, Y) + B(x, Y)) * math.log(x) / (math.log(x) - g), Y)
                   for Y in sorted([10 ** k for k in range(1, 8)] + [3 * 10 ** k for k in range(1, 7)]) if Y < x / 10)
        print(f"  x = {x:.0e}: |m(x)| log x <= {v:.4f}  (Y = {Y:.0e})")
