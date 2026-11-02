"""Rigorous check of the corrected [H, (5.36)] (`integral_H2_le`, MinorArcs/TypeIIS1.lean), v = 2:

    int_1^T H2(S) dS/S <= 0.15107 log T + 0.0231   for all T >= 1   (C2 = 0.023059...),

where H2(S) = (4/pi^2) max(T2(S), 0) for S < 16, H2(S) = 0.15107 for S >= 16, and
T2(S) = sum_{s <= S odd} (1/s) int_{1/2}^1 g2(uS/s) du,  g2(x) = sum_{r1, r2 <= x, (r1, r2) = 1,
r1 r2 odd} mu(r1) mu(r2)/(sigma(r1) sigma(r2))  ([H, (5.19), Lemma 5.1.2]).

[H, (5.32)] claims int_1^T G2(S) dS/S <= 0.37273 log T (G2 >= T2), i.e. C2 = 0; this is false:
int_1^4 T2(S) dS/S = (log 2 - 1/2) + (1/2) log(3/2) + (1/3) log(4/3) + 1/24 = 0.53344 > 0.37273 log 4.

For S >= 16 the integrand is 0.15107/S, so the excess d(T) = int_1^T H2/S - 0.15107 log T is constant
there and C2 = sup_{1 <= T <= 16} d(T).  On [1, 16] T2 is piecewise of the form alpha + beta/S (g2 is
a step function, so int_0^y g2 is piecewise linear); the integrals are exact rationals times logs,
evaluated in interval arithmetic.  Within a piece the integrand H2(S) - 0.15107 changes sign at most once, so the maximum of d on
the piece is at an endpoint or at that sign change; all three are evaluated.

Also checks `H2_le` ([H, (5.37)]): T2(S) <= 1/2 on [1, 16) (exact; equality on [2, 3)), so
H2 <= (4/pi^2)(1/2) = 2/pi^2 there, and H2 = 0.15107 < 2/pi^2 for S >= 16.

Usage: python3 scripts/h2_integral_check.py   (seconds; needs sympy, mpmath)
"""
from fractions import Fraction as Fr
import math
from sympy import divisor_sigma, mobius
from mpmath import iv

iv.dps = 30
N = 32
w = [Fr(0)] * (N + 1)
for r in range(1, N + 1, 2):
    m = int(mobius(r))
    if m:
        w[r] = Fr(m, int(divisor_sigma(r)))
g2 = [sum((w[a] * w[b] for a in range(1, n + 1) for b in range(1, n + 1) if math.gcd(a, b) == 1), Fr(0))
      for n in range(N + 1)]
C = [Fr(0)]
for n in range(N):
    C.append(C[-1] + g2[n])                     # C[k] = int_0^k g2

bp = {Fr(1), Fr(16)}                            # breakpoints: S/s or S/(2s) an integer, s odd <= 15
for s in range(1, 16, 2):
    for k in range(0, 40):
        for d in (s, 2 * s):
            if 1 < k * d < 16:
                bp.add(Fr(k * d))
bp = sorted(bp)

def coeffs(a, b):
    """T2(S) = alpha + beta/S on (a, b)."""
    mid = (a + b) / 2
    alpha = Fr(0); beta = Fr(0)
    for s in range(1, math.floor(mid) + 1, 2):
        for d, sign in ((s, 1), (2 * s, -1)):
            k = math.floor(mid / d)             # G(S/d) = C[k] + (S/d - k) g2[k] on the piece
            alpha += sign * g2[k] / d
            beta += sign * (C[k] - k * g2[k])
    return alpha, beta

def I(q):
    return iv.mpf(q.numerator) / q.denominator

c4 = 4 / iv.pi ** 2
c = iv.mpf('0.15107')
def J(al, be, x, y):
    """int_x^y (c4 (al + be/S) - c)/S dS, x, y intervals."""
    return c4 * (I(al) * (iv.log(y) - iv.log(x)) + I(be) * (1 / x - 1 / y)) - c * (iv.log(y) - iv.log(x))
d = iv.mpf(0); best = iv.mpf(0); T2max = Fr(0)
for a, b in zip(bp, bp[1:]):
    al, be = coeffs(a, b)
    assert al + be / b >= 0 and al + be / a >= 0          # T2 >= 0 on [1, 16]
    # H2_le ([H, (5.37)]): T2 <= 1/2 on [1, 16); T2 = al + be/S is monotone on the piece.
    T2max = max(T2max, al + be / a, al + be / b)
    # on (a, b) the integrand c4(al + be/S) - c changes sign at most once, at S* = c4 be/(c - c4 al);
    # so max_{[a,b]} d is attained at a, b or S*.
    den = c - c4 * I(al)
    if den.a > 0 or den.b < 0:
        Ss = c4 * I(be) / den
        if Ss.a > I(a).b and Ss.b < I(b).a:
            # d(S*) in interval arithmetic: evaluate J on [a, S*] with S* as an interval
            v = d + J(al, be, I(a), Ss)
            if v.b > best.b:
                best = v
    d = d + J(al, be, I(a), I(b))
    if d.b > best.b:
        best = d
    if b == 4:
        print("d(4) =", d, " (> 0: [H, (5.32)] fails at T = 4)")
print("max T2 on [1, 16] =", T2max, "=", float(T2max))
assert T2max <= Fr(1, 2)
print("OK (H2_le): T2(S) <= 1/2 on [1, 16), so H2(S) <= 2/pi^2 everywhere")
print("d(16) =", d)
print("sup_{T >= 1} d(T) <=", best.b)
assert best.b < 0.0231
print("OK: int_1^T H2(S)/S dS <= 0.15107 log T + 0.0231 for all T >= 1")
