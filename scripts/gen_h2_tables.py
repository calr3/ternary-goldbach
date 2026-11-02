"""Generate the data of TernaryGoldbach/MinorArcs/H2Bound.lean and re-run its rational checks.

On [n, n+1), 1 <= n <= 15:  T2(S) = alpha_n + beta_n/S  (exact rationals, from [H, (5.19)]);
log bounds lo_j <= log j < hi_j (units 10^-9) for j <= 16;  k = 4/pi^2 in [kLo, kHi].
The Lean file re-checks everything with `decide +kernel`.

Usage: python3 scripts/gen_h2_tables.py   (prints the Lean definitions)
"""
from fractions import Fraction as F
import math
from mpmath import mp, log as mlog, mpf

mp.dps = 40
mu = [0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1]
sig = [0, 1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24]

def cf(a, b):
    if math.gcd(a, b) == 1 and (a * b) % 2 == 1:
        return F(mu[a] * mu[b], sig[a] * sig[b])
    return F(0)

def AB(n):
    A = F(0); B = F(0)
    for s in range(1, n + 1):
        if s % 2 == 0:
            continue
        for a in range(1, n // s + 1):
            for b in range(1, n // s + 1):
                m = max(a, b)
                if 2 * s * m <= n:
                    A += cf(a, b) * F(1, 2 * s)
                else:
                    A += cf(a, b) * F(1, s); B += cf(a, b) * (-m)
    return A, B

ab = [(F(0), F(0))] + [AB(n) for n in range(1, 16)]
D = 10 ** 9
lo = [0, 0] + [int(mp.floor(mlog(j) * D)) - 3 for j in range(2, 17)]
hi = [0, 1] + [int(mp.ceil(mlog(j) * D)) + 3 for j in range(2, 17)]
kHi = F(4) / F(314159265358979323846, 10 ** 20) ** 2
kLo = F(4) / F(314159265358979323847, 10 ** 20) ** 2
c = F(15107, 100000)
loQ = lambda j: F(lo[j], D)
hiQ = lambda j: F(hi[j], D)
Pu = lambda j: ab[j][0] * (hiQ(j + 1) - loQ(j)) + ab[j][1] * (F(1, j) - F(1, j + 1))
PU = lambda m: sum((Pu(i + 1) for i in range(m - 1)), F(0))
E15 = max(F(0), kHi * (ab[15][0] + ab[15][1] / 15) - c) / 16
for n in range(1, 16):
    a, b = ab[n]
    assert a >= 0 and 0 <= a + b / n <= F(1, 2) and 0 <= a + b / (n + 1) <= F(1, 2)
for n in range(2, 15):
    a, b = ab[n]
    assert b >= 0 and c <= kLo * (a + b / (n + 1)), n
assert ab[1] == (1, -1) and kHi * ab[15][0] <= c and kHi / 3 < c and kHi / 3 - 5 * c / 6 <= F(231, 10000)
worst = 0
for m in range(3, 17):
    v = kHi * PU(m) - c * loQ(m) + (E15 if m == 15 else 0)
    assert PU(m) >= 0 and v <= F(231, 10000), (m, float(v))
    worst = max(worst, v)
print(f"-- max over m of the D-bound: {float(worst):.9f} (need <= 0.0231)")
print("def abT : List (ℚ × ℚ) := [" + ", ".join(f"({a.numerator}/{a.denominator}, {b.numerator}/{b.denominator})" for a, b in ab) + "]")
print("def loN : List ℕ := [" + ", ".join(map(str, lo)) + "]")
print("def hiN : List ℕ := [" + ", ".join(map(str, hi)) + "]")
