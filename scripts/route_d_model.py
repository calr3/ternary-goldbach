"""Route D model check (NOTES, "Büthe and sources available by 2014"): does the minor-arc total
still close if Büthe's |psi(x) - x| <= 0.94 sqrt(x) is replaced by the partial-RH bound
|psi(x) - x| <= c(x) sqrt(x), c(x) = log(x)^2 / (8 pi)    [Büthe, arXiv:1410.7015, Thm 2]?

Approximate model, not certified: the Theorem 3.1.1 and cell models of `prelim_sensitivity.py`.
The literature constants that the partial-RH bound weakens are made functions of
V = floor(9 x^{1/3} / 2), the argument at which the Lean proof applies them
(`TypeI2Sum`, `TypeI2Large`; V >= 2.7e7 since x >= 2.16e20):
* (2.14) psi(V) <= a14 V,               a14 = 1 + c(V)/sqrt(V);
* (2.17) sum_{n<=V} Lambda(n) n <= a17 V^2/2,
         a17 = 1 + (10/3) c(V)/sqrt(V)  (V psi(V) - int_0^V psi, with c increasing);
* (2.19) is used for W in [V, x/U] (`TypeIITotal`). There
         sum_{W/2<p<=W} log^2 p <= log W (theta(W) - theta(W/2)) - 0.1534 W + ...,
         and 1.71 c(W) sqrt(W) log W <= 0.1534 W for W >= 2.7e7, so a19 = 1/2 is kept;
* (5.5), (2.12), (2.15) keep their constants (kernel checks plus the partial-RH bound).
The Mertens-product constant 2.50637 (Lemma C.2.2) is also varied, in case the weaker input
forces a larger one in Lean.

Usage: python3 scripts/route_d_model.py   (about 5 minutes)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prelim_sensitivity as ps  # noqa: E402
from mpmath import mpf, sqrt, log, pi, floor  # noqa: E402


def c(y):
    return log(y) ** 2 / (8 * pi)


def Vof(x):
    return floor(9 * x ** (mpf(1) / 3) / 2)


def consts(V):
    a14 = 1 + c(V) / sqrt(V)
    a17 = 1 + mpf(10) / 3 * c(V) / sqrt(V)
    return a14, a17


def min_const_route_d(extra):
    """`ps.min_const` with a14, a17 depending on V(x)."""
    need = mpf('-10')
    for (x, d, q, phi, phi2q) in ps.PTS:
        a14, a17 = consts(Vof(x))
        P = dict(ps.BASE)
        P.update(dict(a14=a14, a17=a17))
        P.update(extra)
        ours = ps.model(P)
        d0 = max(2, abs(d) / 4)
        t = d0 * q
        rest = 2.5 * x / sqrt(t) + 2 * x / t * ps.Lf(t, q, phi) + mpf('3.8') * x ** (mpf(5) / 6)
        C = (ours(x, d, q, phi, phi2q) - rest) * sqrt(d0 * phi) / x - ps.R(x, t) * log(t)
        need = max(need, C)
    return need


def run(name, extra, C0):
    C = min_const_route_d(extra)
    Cl = mpf('0.8764') + max(0, C - C0)
    # second case (heuristic, as in prelim_sensitivity): psi ratio at the smallest V
    a14, a17 = consts(Vof(mpf('2.16e20')))
    psi_ratio = max(a14 / ps.BASE['a14'], a17 / ps.BASE['a17'])
    Fc2 = extra.get('Fc2', ps.BASE['Fc2'])
    Z = ps.Ztot_worst(Cl, mpf('3.8'), mpf('0.276'), 1234 * psi_ratio, ps.BASE['Fc1'], Fc2)
    ok = 'OK (<= 1.037)' if Z <= mpf('1.037') else 'FAILS'
    print(f"{name:44s} model C={float(C):.4f}  Lean C={float(Cl):.4f}  h2={float(1234 * psi_ratio):6.0f}"
          f"  worst Z={float(Z):.4f}  {ok}")


if __name__ == "__main__":
    for V in [Vof(mpf(s)) for s in ['2.16e20', '1e22', '1e27', '1e40']]:
        a14, a17 = consts(V)
        print(f"V = {float(V):.3e}: c(V) = {float(c(V)):6.2f}, a14 = {float(a14):.5f}, a17 = {float(a17):.5f}")
    print()
    C0 = ps.min_const(ps.BASE)
    Zb = ps.Ztot_worst(mpf('0.8764'), mpf('3.8'), mpf('0.276'), 1234, ps.BASE['Fc1'], ps.BASE['Fc2'])
    print(f"baseline (Büthe): model C = {float(C0):.4f}, Lean C = 0.8764, worst Z = {float(Zb):.4f}")
    run("route D", {}, C0)
    run("route D, (5.5) 1.4262 -> 2", dict(a55=mpf(2)), C0)
    run("route D, Mertens 2.50637 -> 3.5", dict(Fc2=mpf('3.5')), C0)
    run("route D, Mertens 2.50637 -> 5", dict(Fc2=mpf(5)), C0)
