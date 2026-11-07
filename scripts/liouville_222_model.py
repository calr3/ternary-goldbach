"""What [H, (2.22)] with constant 2.8 needs from a Moebius bound: float model of Ramare's Liouville
route (Prelim/LiouvilleBound.lean).
|l(z)| log z <= c_l for z >= 1e5 from l(z) = sum_{u^2<=z} m(z/u^2)/u^2 with |m(y)| <= sqrt(2/y) (y < 11815,
kernel) and |m(y)| <= B(y) beyond; then y * sum_u |mu(u)|/u^2 min(5/3, c_l/(y - 2 log u)) <= c22. For y >= 80 the Lean proof gives
(20/9) c_l + 0.006, so keeping 2.8 needs c_l <= 1.25, i.e. K <= about 0.65 in K/(log x - 0.7521).

Usage: python3 scripts/liouville_222_model.py"""
import math
def mu_list(N):
    mu = [1]*(N+1); mu[0] = 0; isp = [True]*(N+1)
    for p in range(2, N+1):
        if isp[p]:
            for q in range(2*p, N+1, p): isp[q] = False
            for q in range(p, N+1, p): mu[q] = -mu[q]
            for q in range(p*p, N+1, p*p): mu[q] = 0
    return mu
import numpy as np
def c_liou(B, zs):
    best = 0.0
    for z in zs:
        u = np.arange(1, int(math.isqrt(int(z))) + 1, dtype=np.float64)
        y = z / (u * u)
        t = np.where(y >= 11815, B(np.maximum(y, 11815.0)), np.sqrt(2 / y)) / (u * u)
        best = max(best, float(t.sum()) * math.log(z))
    return best
zs = [10 ** (5 + k / 40) for k in range(0, 281)]          # 1e5 .. 1e12
MU = mu_list(200000)
def c22(cl):
    best = 0.0
    for k in range(0, 800):
        y = 2.8 + k * 0.1                                  # y in [2.8, 203)
        s = 0.0
        U = min(int(math.exp(y / 2)), 200000)
        for u in range(1, U + 1):
            if MU[u] == 0: continue
            w = y - 2 * math.log(u)
            b = 5 / 3 if w <= 0 else min(5 / 3, cl / w)
            s += b / (u * u)
        best = max(best, y * s)
    return best
for name, B in [("Ramare 0.03/log y", lambda y: 0.03 / np.log(y)),
                ("own 0.55/(log y - 0.7521)", lambda y: 0.55 / (np.log(y) - 0.7521))]:
    cl = max(0.7831, c_liou(B, zs))     # 0.7831 = kernel max for z <= 1e5
    print(f"{name}: Liouville constant c_l = {cl:.4f}; (2.22) constant ~ {c22(cl):.3f}")
print("Lean: c_l = 0.99, (2.22) constant 2.8")
