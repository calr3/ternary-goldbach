"""Sensitivity of the minor-arc total to the literature bounds in Prelim/.

Question: if a `Prelim/` bound is replaced by a weaker one that is easier to prove (elementary,
or with a smaller computation), does the proof still close?  Two layers, both approximate models
of the Lean statements (not certified):

Layer 2 (Theorem 3.1.1, first case, q <= x^{1/3}/6).  The model of `thm_3_1_1_numerics.py`
(the right-hand sides of typeI1_le, typeI2_le_*, typeII_637/640 + 3 log x) with every Prelim
constant as a parameter.  We bisect for the smallest constant C (0.8764 in Lean) such that the
model stays below Theorem 3.1.1's form `(R log t + C)/sqrt(d0 phi) x + ...` on the same grid.

Second case (q > x^{1/3}/6): 0.276 x^{5/6} log^{3/2} x comes from the Type II main term
sqrt(12 F0 X0 B0) T^{5/2}; we scale it by sqrt of the factors on F0 (Lemma C.2.2) and X0 (the S2
side: (2.19) and the large sieve).  1234 x^{2/3} log x (Type I and lower-order terms) is scaled
linearly by the psi-constant ratio.  These two scalings are heuristics, not re-derivations.

Layer 1 (the minor-arc total, repair 3).  The cell model of `minor_arc_cells_check.py` with the
Theorem 3.1.1 constants and Lemma C.2.2's F(r) as parameters.  Lean needs Z <= 1.037
(`NumericsGoal`); the true limit is about 1.058 minus the non-prime term.

Usage: python3 scripts/prelim_sensitivity.py
"""
import random
from mpmath import mp, mpf, sqrt, log, pi, e, zeta, floor, exp, euler
from sympy import totient

mp.dps = 20

BASE = dict(
    a23=mpf('1.00303'),   # (2.23)  |sum mu(n)/n log(x/n)| <= a23 q/phi(q)
    a22=mpf('0.8'),       # (2.22)  |sum mu(n)/n| <= a22 (q/phi)/log(x/q); None = drop (use (2.20))
    a14=mpf('1.0004'),    # (2.14)  psi(y) <= a14 y, y >= 2e6
    a15=mpf('1.03883'),   # (2.15)  psi(y) < a15 y
    a17=mpf('1.0008'),    # (2.17)  sum Lambda(n) n < a17 y^2/2
    a55=mpf('1.4262'),    # (5.5)   psi - theta < a55 sqrt(y)
    a12=mpf('0'),         # (2.12)  sum Lambda(n)/n <= log x + a12
    a19=mpf('0.5'),       # (2.19)  sum_{y/2<p<=y} log^2 p <= a19 y log y
    lam=mpf('1'),         # large sieve: factor on the S2 side (1 = Montgomery-Vaughan)
    Fc1=exp(euler),       # Lemma C.2.2: q/phi(q) < Fc1 loglog r + Fc2/loglog r
    Fc2=mpf('2.50637'),
)

c0 = mpf('31.521'); c2 = 6 * pi / (5 * sqrt(c0)); L1 = 8 * log(2)
zeta3 = mpf('1.27') * zeta(mpf(1.5)) ** 3


def logPlus(y): return max(log(y), 0) if y > 0 else 0
def minInv(c, d): return 1 if d == 0 else min(1, c / d ** 2)
def logFB(d): return 2 - log(4) if d == 0 else min(2 - log(4), 96 * log(2) / (pi * d) ** 2)


def model(P):
    def muBound(U, q, tq):
        if P['a22'] is not None and 2 * q * q < U:
            return min(1, P['a22'] * (2 * q / tq) / log(U / (2 * q * q)))
        return 1

    def b441(x, q, D):
        c1 = 1 + L1 / (x / D)
        return (2 * sqrt(c0 * c1) / pi * D * log(e * x / D) + 3 * c1 / 2 * (x / q) * logPlus(D / (c2 * x / q)) * log(q / c2)
                + (2 * L1 / pi * max(1, log(c0 * e ** 3 * q * q / (4 * pi * L1 * x))) * log(x)
                   + 2 * sqrt(c0 * c1) / pi * (sqrt(3) + 0.5 * logPlus(D / (q / 2))) * log(q / c2)) * q
                + 3 * c1 / 2 * sqrt(2 * x / c2) * log(2 * x / c2) + 20 * c0 * c2 ** 1.5 / (3 * pi ** 2) * sqrt(2 * x) * log(2 * e * x / c2))

    def typeI1(x, d, q, U, phi2q):
        return (x / (2 * q) * minInv(c0, pi * d) * (P['a23'] * (2 * q / phi2q) + log(x / U) * muBound(U, q, phi2q))
                + x / (2 * q) * logFB(d) * muBound(U, q, phi2q) + c0 * (0.5 - 2 / pi ** 2) * (U ** 2 / (4 * q * x) * log(exp(0.5) * x / U) + 1 / e)
                + b441(x, q, U))

    def cPlus(x, U, V): return 1 + L1 / (x / (U * V))
    def coefUV(c): return 2 * sqrt(c0 * c) / pi + 3 * c / (2 * c2 * e)

    def coefQ(x, q, U, V, c):
        return (sqrt(c0 * c) / pi * (logPlus(2 * U / q) + 1 / e) + 2 * L1 / pi * max(1, log(c0 * e ** 3 * q * q * V / (4 * pi * L1 * x)))
                + (2 * sqrt(3 * c0 * c) / pi + 3 * c / (2 * c2) + 55 * c0 * c2 / (6 * pi ** 2)))

    def typeI2(x, d, q, Q, U, V, phi2q, eps=mpf('0.07')):
        a14, half17 = P['a14'], P['a17'] / 2
        M0 = min(Q / (2 * V), U)
        common = (x / (2 * q) * minInv(c0, pi * d) * muBound(M0, q, phi2q) * (log(V * q) + P['a12'])
                  + c0 * (mpf(1) / 8 - 1 / (2 * pi ** 2)) / x * (U ** 2 / q * (half17 * V ** 2 + V * q * log(q)) + (2 * U + q) * half17 * V ** 2))
        c = cPlus(x, U, V)
        if abs(d) <= 1 / (2 * c2):
            return common + a14 * coefUV(c) * U * V + a14 * coefQ(x, q, U, V, c) * Q
        ad = abs(d)
        return (common + a14 * (2 * sqrt(c0 * c) / pi * (1 + (1 + eps) * (1 + V / Q) / e)) * U * V
                + a14 * (1.5 * c * (2 + (1 + eps) / eps * logPlus(2 * U * V * ad * q / x))) * (x * V / Q)
                + a14 * (35 * c0 * c2 / (3 * pi ** 2)) * Q
                + 2 * sqrt(c0 * c) / pi * (1 + eps) * sqrt(3 + 2 * eps) * (x / (ad * q) * (P['a15'] + log(q) + logPlus(6 * U * V * ad * q / (sqrt(2) * x))) + a14 * V))

    def kap1(x, U, V): return 2 / pi ** 2 + zeta3 * sqrt(x / V) / U
    S2f = P['lam'] * P['a19'] / mpf('0.5')

    def typeII637(x, q, U, V, phi):
        L0 = log(x / (U * V))
        return (x / sqrt(2 * phi) * sqrt(S2f * (L0 + log(2 * q) * (log(log(x / U / (2 * q))) - log(log(V / (2 * q))))) * (mpf('0.60428') * L0 + 8 * zeta3 * sqrt(x / V) / U))
                + sqrt(S2f) * 4 * sqrt(kap1(x, U, V) * q * x / (2 * phi)) * (2 * sqrt(x / U) + sqrt(log(2 * q)) * (2 * e * sqrt(2 * q) + 4 * sqrt(x / U / log(x / U / (2 * q)))))
                + 8 * P['a55'] * x * sqrt(kap1(x, U, V) * (0.5 + 1 / U)) / sqrt(V))

    def typeII640(x, d, q, Q, U, V, phi):
        ad = abs(d); c = ad * q * (1 + x / (2 * U * Q)) / 4; L0 = log(x / (U * V))
        return (2 * x / sqrt(ad * phi) * sqrt(S2f * (L0 + log(c) * (log(log(x / U / c)) - log(log(V / c)))) * (mpf('0.60428') * L0 + 8 * zeta3 * sqrt(x / V) / U))
                + sqrt(S2f) * 4 * sqrt(kap1(x, U, V) * q * x / (2 * phi)) * (2 * sqrt(x / U) + sqrt(log(c)) * (2 * e * sqrt(c) + 4 * sqrt(x / U / log(x / U / c))))
                + 8 * P['a55'] * x * sqrt(kap1(x, U, V) * (0.5 + 1 / U)) / sqrt(V))

    def ours(x, d, q, phi, phi2q):
        t3 = x ** (mpf(1) / 3); Q = mpf(3) / 4 * t3 ** 2; d0 = max(2, abs(d) / 4)
        U = floor(t3 ** 2 / (9 * sqrt(q * d0))); V = floor(9 * t3 / 2)
        ii = typeII637(x, q, U, V, phi)
        if abs(d) >= 8:
            ii = min(ii, typeII640(x, d, q, Q, U, V, phi))
        return typeI1(x, d, q, U, phi2q) + typeI2(x, d, q, Q, U, V, phi2q) + ii + 3 * log(x)
    return ours


def R(x, t): return mpf('0.27125') * log(1 + log(4 * t) / (2 * log(9 * x ** (mpf(1) / 3) / (mpf('2.004') * t)))) + mpf('0.41415')
def Lf(t, q, phi): return q / phi * (mpf(13) / 4 * log(t) + mpf('7.82')) + mpf('13.66') * log(t) + mpf('37.55')


def grid():
    random.seed(1)
    pts = []
    for x in [mpf('2.16e20'), mpf('1e22'), mpf('1e27'), mpf('1e40'), mpf('1e60')]:
        y = x ** (mpf(1) / 3) / 6
        qs = set([1, 2, 3, 6, 30, 210, 2310, 30030, 510510, int(y), int(y / 3)])
        for _ in range(30):
            qs.add(int(10 ** (random.uniform(0, float(log(y, 10))))))
        for q in sorted(qs):
            if q < 1 or q > y:
                continue
            phi = mpf(int(totient(q))); phi2q = mpf(int(totient(2 * q)))
            dmax = float(8 * y / q)
            for d in [0, 0.3, 0.75, 1, 2, 4, 7.99, 8, 16, 300, dmax / 10, dmax]:
                if d <= dmax:
                    pts.append((x, mpf(d), q, phi, phi2q))
    return pts


PTS = grid()


def min_const(P, Rs=1):
    """Smallest C with model <= Thm 3.1.1 form (with 3.8 x^{5/6}) on the grid."""
    ours = model(P)
    need = mpf('-10')
    for (x, d, q, phi, phi2q) in PTS:
        d0 = max(2, abs(d) / 4); t = d0 * q
        rest = 2.5 * x / sqrt(t) + 2 * x / t * Lf(t, q, phi) + mpf('3.8') * x ** (mpf(5) / 6)
        # ours <= (R log t + C) x / sqrt(d0 phi) + rest  <=>  C >= ...
        C = (ours(x, d, q, phi, phi2q) - rest) * sqrt(d0 * phi) / x - Rs * R(x, t) * log(t)
        need = max(need, C)
    return need


# ---- Layer 1: the cell model -------------------------------------------------------------
kappa = 49


def Ztot_worst(C, c56, h1, h2, Fc1, Fc2, Rs=1):
    def F(r): return Fc1 * log(log(r)) + Fc2 / log(log(r))
    def L(t): return F(t / 2) * (mpf(13) / 4 * log(t) + mpf('7.82')) + mpf('13.66') * log(t) + mpf('37.55')
    def gx(z, r): return ((Rs * R(z, 2 * r) * log(2 * r) + C) * sqrt(F(r)) + mpf('2.5')) / sqrt(2 * r) + L(2 * r) / r + c56 * z ** (-mpf(1) / 6)
    def h(z): return h1 * z ** (-mpf(1) / 6) * log(z) ** mpf(1.5) + h2 * z ** (-mpf(1) / 3) * log(z)
    def ghat(y, n): return mpf('1.398') * max(gx(y, n), h(y)) + 17 * (670 / n) ** 3 / 3

    def Mcell(Y, Y2, rho=mpf('1.25')):
        x = kappa * Y; x2 = kappa * Y2; r0 = 150000
        s = lambda x: mpf('0.640209') * log(x) - mpf('0.021095')
        D = lambda x: log(2 * sqrt(x / 784)) + mpf('1.33258')
        Q = sqrt(x / 784); r2 = int(min((2 * Q) ** mpf(0.6) / 2 - 1, Q / 20000))
        sD = s(x) / D(x)
        base = ghat(Y, r0) * ((log(2 * (r0 + 1)) + mpf('1.36')) * sD - mpf('8.6249'))
        mid = 0; N = r0
        while N < r2 - 1:
            N2 = min(int(N * rho) + 1, r2 - 1)
            mid += ghat(Y, N + 1) * log(mpf(N2 + 1) / (N + 1))
            N = N2
        mid *= sD
        c = log(2 * r2) + mpf('1.36')
        tail = ghat(Y, r2) * (s(x2) - c * s(x2) / D(x2))
        return base + mid + tail

    t = mpf('0.004')
    worst = 0
    for (a, b) in [(25.0045, 25.5), (25.5, 26), (26, 27), (27, 28), (28, 30), (30, 34), (34, 42), (42, 58)]:
        M = Mcell(mpf(10) ** a, mpf(10) ** b)
        worst = max(worst, (1 + t) * M + (1 + 1 / t) * 17 * sqrt(pi / 2) * mpf('1e-6'))
    return worst


def run(name, changes):
    P = dict(BASE); P.update(changes)
    # A factor on the S2 side scales the Type II main term, i.e. R log t, by sqrt(S2f).
    Rs = sqrt(P['lam'] * P['a19'] / mpf('0.5'))
    C = min_const(P, Rs)
    C0 = BASE_C
    # second case scalings (heuristic)
    S2f = P['lam'] * P['a19'] / mpf('0.5')
    h1 = mpf('0.276') * sqrt(S2f * P['Fc1'] / BASE['Fc1'])
    psi_ratio = max(P['a14'] / BASE['a14'], P['a15'] / BASE['a15'], P['a17'] / BASE['a17'])
    h2 = 1234 * psi_ratio
    # Lean's 0.8764 is the baseline; shift it by the model's increase.
    Cl = mpf('0.8764') + max(0, C - C0)
    Z = Ztot_worst(Cl, mpf('3.8'), h1, h2, P['Fc1'], P['Fc2'], Rs)
    ok = 'OK (<= 1.037)' if Z <= mpf('1.037') else ('tight (<= 1.05)' if Z <= mpf('1.05') else 'FAILS')
    print(f"{name:52s} R x{float(Rs):.3f} C={float(Cl):7.4f}  h1={float(h1):.3f} h2={float(h2):6.0f}  worst Z={float(Z):.4f}  {ok}")


if __name__ == "__main__":
    BASE_C = min_const(BASE)
    print(f"baseline: model needs C >= {float(BASE_C):.4f} (Lean: 0.8764); "
          f"cell model with Lean constants: Z = {float(Ztot_worst(mpf('0.8764'), mpf('3.8'), mpf('0.276'), 1234, BASE['Fc1'], BASE['Fc2'])):.4f}")
    print()
    print("One bound at a time, replaced by an elementary (or easier) version:")
    run("(2.14)/(2.17) psi <= 1.0004y -> 1.04y", dict(a14=mpf('1.04'), a17=mpf('1.04')))
    run("(2.14)/(2.15)/(2.17) psi -> 1.106y (Chebyshev)", dict(a14=mpf('1.106'), a15=mpf('1.106'), a17=mpf('1.106')))
    run("(2.14)/(2.15)/(2.17) psi -> 1.39y (log 4)", dict(a14=mpf('1.39'), a15=mpf('1.39'), a17=mpf('1.39')))
    run("(2.12) sum Lambda/n <= log x + 0.4", dict(a12=mpf('0.4')))
    run("(5.5) psi - theta < 2 sqrt y", dict(a55=mpf('2')))
    run("(2.19) 1/2 -> log 2 (binomial-coefficient bound)", dict(a19=log(2)))
    run("(2.22) dropped (use (2.20) only)", dict(a22=None))
    run("(2.23) 1.00303 -> 2", dict(a23=mpf('2')))
    run("C.2.2 e^gamma -> 2.4 (elementary Mertens)", dict(Fc1=mpf('2.4')))
    run("C.2.2 e^gamma -> e^{1.32} = 3.74 (crude)", dict(Fc1=exp(mpf('1.32'))))
    for lam in ['1.5', '2', '3.1416', '12.566']:
        run(f"large sieve: S2 side x {lam}", dict(lam=mpf(lam)))
    print()
    print("Combined:")
    run("all psi-type -> 1.106, (2.12)+0.4, (5.5) 2, (2.19) log2", dict(
        a14=mpf('1.106'), a15=mpf('1.106'), a17=mpf('1.106'), a12=mpf('0.4'), a55=mpf('2'), a19=log(2)))
    run("  ... + (2.22) dropped, (2.23) 2", dict(
        a14=mpf('1.106'), a15=mpf('1.106'), a17=mpf('1.106'), a12=mpf('0.4'), a55=mpf('2'), a19=log(2),
        a22=None, a23=mpf('2')))
    run("  ... + C.2.2 e^gamma -> 2.4", dict(
        a14=mpf('1.106'), a15=mpf('1.106'), a17=mpf('1.106'), a12=mpf('0.4'), a55=mpf('2'), a19=log(2),
        a22=None, a23=mpf('2'), Fc1=mpf('2.4')))
    run("all psi-type -> 1.106, (2.12)+0.4, (5.5) 2, (2.23) 2", dict(
        a14=mpf('1.106'), a15=mpf('1.106'), a17=mpf('1.106'), a12=mpf('0.4'), a55=mpf('2'), a23=mpf('2')))
    for a22 in ['1.5', '3']:
        run(f"(2.22) 4/5 -> {a22}", dict(a22=mpf(a22)))
    print()
    print("Break-even (worst Z = 1.037), one parameter at a time:")

    def Zof(changes):
        P = dict(BASE); P.update(changes)
        Rs = sqrt(P['lam'] * P['a19'] / mpf('0.5'))
        Cl = mpf('0.8764') + max(0, min_const(P, Rs) - BASE_C)
        h1 = mpf('0.276') * sqrt(Rs ** 2 * P['Fc1'] / BASE['Fc1'])
        psi_ratio = max(P['a14'] / BASE['a14'], P['a15'] / BASE['a15'], P['a17'] / BASE['a17'])
        return Ztot_worst(Cl, mpf('3.8'), h1, 1234 * psi_ratio, P['Fc1'], P['Fc2'], Rs)

    def breakeven(name, f, lo, hi):
        for _ in range(14):
            mid = (lo + hi) / 2
            if Zof(f(mid)) <= mpf('1.037'):
                lo = mid
            else:
                hi = mid
        print(f"  {name}: up to {float(lo):.4f}")

    breakeven("large-sieve factor on S2 (sharp = 1)", lambda v: dict(lam=v), mpf(1), mpf(2))
    breakeven("C.2.2 coefficient of loglog r (e^gamma = 1.7811)", lambda v: dict(Fc1=v), exp(euler), mpf(3))
    breakeven("psi(y) <= a y, all of (2.14)/(2.15)/(2.17)", lambda v: dict(a14=v, a15=v, a17=v), mpf('1.04'), mpf('1.6'))
    breakeven("(2.22) constant (4/5)", lambda v: dict(a22=v), mpf("0.8"), mpf("200"))
