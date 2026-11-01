"""Re-run [B, §14.3] (the minor-arc total (14.49)) with our corrected Theorem 3.1.1.

[B]'s Theorem 3.1.1 has `R log(δ₀q) + 0.5` and `3.36 x^{5/6}`; what we prove
(`MinorArcs/PointwiseBound.lean`) has `0.8764` and `3.8`.  Both constants enter
g_{y,φ}(r) (11.19)/(13.10), and through it the three parts of M (13.13):

* (14.37)  g(r0) · (… S − (√J − √E)²) ≤ g(r0) · 9.2598 x,
* (14.43)  (7/15) g(r1) S,
* (14.47)  2S/(log x + 2c⁻) ∫_{r0}^{r1} g(r)/r dr ≤ 1.280418 x (f0 + f1 + f2)   (13.33),

where only f1 (its first term, from the `+0.5`) and f2 (from `3.36`) change; f0 does not
involve either constant.  Everything else (S, J, E, T, the bound f0 ≤ 0.071498, which [B]
gets by bisection) is taken from [B] as is.

Usage: python3 scripts/minor_arc_total_numerics.py
"""

from mpmath import mp, mpf, log, sqrt, e, euler, pi, exp

mp.dps = 30
EG = exp(euler)
KAPPA = 49
R0 = mpf(150000)
CGAMMA = mpf("1.025742")


def Fcal(r):
    """Ϝ(r) = e^γ log log r + 2.50637 / log log r (Lemma C.2.2's bound for q/φ(q))."""
    return EG * log(log(r)) + mpf("2.50637") / log(log(r))


def M_parts(c, c56, y=mpf(10) ** 25):
    x = KAPPA * y
    # (14.37)
    g_r0 = ((mpf("0.58385") * log(300000) + c) * sqrt(mpf("5.42506")) + mpf("2.5")) / sqrt(2 * R0) \
        + mpf("474.608") / R0 + c56 * (log(y) / (2 * y)) ** (mpf(1) / 6)
    m1 = g_r0 * mpf("9.2598")
    # (14.43), at y (the bound is decreasing in y; we scan y below)
    r1 = mpf(3) / 8 * y ** (mpf(4) / 15)
    ly, lly = log(y), log(log(y))
    sqF = sqrt(EG * lly - mpf("1.43644"))
    g_r1 = ((mpf("0.71219") * log(mpf(3) / 4 * y ** (mpf(4) / 15)) + c) * sqF + mpf("2.5")) \
        / sqrt(mpf(3) / 4 * y ** (mpf(4) / 15)) \
        + (mpf("2.13522") * ly + mpf("18.118")) * lly / r1 \
        + c56 * (ly / 2) ** (mpf(1) / 6) / y ** (mpf(1) / 6)
    m2 = mpf(7) / 15 * g_r1 * (mpf("0.640209") * log(x) - mpf("0.021095"))
    # (14.47): f0 + f1 + f2
    lr0 = log(R0)
    F0 = EG * log(lr0) + CGAMMA
    J = Fcal(R0)  # J_{r0}: [B] uses the same Ϝ bound as for L_{2r0}
    f1 = sqrt(F0) / sqrt(2 * R0) * (1 + EG / (F0 * lr0)) * (c / mpf("0.5")) \
        + 5 / sqrt(2 * R0) \
        + ((mpf(13) / 4 * log(e * R0) + mpf("11.07")) * J + mpf("13.66") * log(e * R0) + mpf("37.55")) / R0
    f2 = c56 * (ly / 2) ** (mpf(1) / 6) / y ** (mpf(1) / 6) * log(r1 / R0)
    f0 = mpf("0.071498")
    m3 = mpf("1.280418") * (f0 + f1 + f2)
    return g_r0, m1, m2, f1, f2, m3


def report(c, c56):
    g_r0, m1, m2, f1, f2, m3 = M_parts(c, c56)
    # (14.43) is decreasing in y: check on a grid
    m2max = max(M_parts(c, c56, mpf(10) ** k)[2] for k in range(25, 400))
    M = m1 + m2max + m3
    phi1 = sqrt(pi / 2)
    Z = (sqrt(phi1 * (M + mpf("3.5776e-4"))) + sqrt(mpf("1.0532e-11"))) ** 2
    print(f"c = {c}, x^(5/6) constant {c56}")
    print(f"  g(r0) = {float(g_r0):.6f}   (14.37) {float(m1):.6f}")
    print(f"  (14.43) max over y >= 1e25: {float(m2max):.6f}")
    print(f"  f1 = {float(f1):.7f}, f2 = {float(f2):.7f}   (14.47) {float(m3):.6f}")
    print(f"  M <= {float(M):.6f}   Z <= {float(Z):.6f} x^2/κ   "
          f"margin vs major arcs 1.058259: {float(mpf('1.058259') - Z):.6f}")
    return Z


def lemma_11_2_1(c, c56):
    """[B, Lemma 11.2.1]: h(x_r) ≥ g_{x_r}(r) at x_r = (6r)³ (r ≥ 11).  Returns the
    worst ratio g/h on a grid of log x_r (with L_{2r} using Ϝ(r) for q/φ(q), as in [B])."""
    worst = (0, None)
    import mpmath
    for i in range(0, 4000):
        lx = log(mpf(66) ** 3) + mpf(i) / 20
        xr = exp(lx)
        r = xr ** (mpf(1) / 3) / 6
        t = 2 * r
        Rx = mpf("0.27125") * log(1 + log(4 * t) / (2 * log(9 * xr ** (mpf(1) / 3) / (mpf("2.004") * t)))) \
            + mpf("0.41415")
        Fr = Fcal(r) if log(log(r)) > 0.5 else mpf(10)
        L = Fcal(t / 2) * (mpf(13) / 4 * log(t) + mpf("7.82")) + mpf("13.66") * log(t) + mpf("37.55")
        g = ((Rx * log(t) + c) * sqrt(Fr) + mpf("2.5")) / sqrt(t) + L / r + c56 * xr ** (-mpf(1) / 6)
        h = mpf("0.276") * xr ** (-mpf(1) / 6) * lx ** mpf(1.5) + 1234 * xr ** (-mpf(1) / 3) * lx
        if g / h > worst[0]:
            worst = (g / h, lx)
    return worst


if __name__ == "__main__":
    Zb = report(mpf("0.5"), mpf("3.36"))
    print("  ([B] (14.49): 1.00948)\n")
    Zc = report(mpf("0.8764"), mpf("3.8"))
    for c, c56 in [(mpf("0.5"), mpf("3.36")), (mpf("0.8764"), mpf("3.8"))]:
        w, lx = lemma_11_2_1(c, c56)
        print(f"Lemma 11.2.1 (c = {c}, {c56}): max g_(x_r)(r)/h(x_r) = {float(w):.4f} at log x_r = {float(lx):.2f}")
