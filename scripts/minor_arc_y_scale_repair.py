"""A repair of [H, Thm 13.2.1] / §14.3 that works entirely with the arcs at scale y = x/κ.

Background (NOTES "Ch. 13: scale erratum"): [H] derives the ℓ∞ bound for S_{η_*} only off the
arcs 𝔐_{8,r}(y), but uses the ℓ² bound and the major arcs at scale x.  The repair:

* Prop 13.1.2 with the family  M_{r₀} = 𝔐_{8,r₀}(x),  M_n = 𝔐_{8,n}(y) = 𝔐_{392,n}(x) (n > r₀).
  The base term keeps [H]'s I₀ ≥ (√J − √E)² ≥ 8.6297x over 𝔐_{8,r₀}(x).
* ℓ²: Cor 12.2.5 (12.42) with δ₀ = 392 (so c⁻ → c⁻ − log 7).
* ℓ∞ off 𝔐_{8,n}(y) ("Prop 11.2.3'"): for each w take a FRESH Dirichlet approximation
  2α = a_w/q_w + δ_w/(wy) at scale wy.  Since α ∉ 𝔐_{8,n}(y), r_w = max(1,|δ_w|/8) q_w ≥
  min(1, w) n (OffArcs.lean).  Thm 3.1.1 at scale wy then gives
  b(w) = max(g_{wy}(min(1,w) n), h(wy)) (first case: r_w ≤ (wy)^{1/3}/6 always, so the
  antitonicity of g on [670, (wy)^{1/3}/6] applies; second case: h), or 17 (trivial) where
  wy < 2.16·10²⁰ or min(1,w) n < 670.  No δ ↦ wδ issue arises (cf. the Prop 11.2.3 erratum).
* Levels up to r₂ ≈ x^{0.3}, the limit of (12.42) (2Q₀ ≤ (2Q)^{0.6}, (20000Q₀)² ≤ x/784),
  instead of [H]'s r₁ = (3/8)y^{4/15}; this shrinks the tail (14.43), which dominates.
* The base gap 𝔐_{8,r₀}(y) \\ 𝔐_{8,r₀}(x) needs |S_{η_*}| ≤ |φ|₁ g(r₀) y ≈ 0.0555 y there.
  [H, Cor 7.1.3] (q ≤ 300000, |δ| ≤ 1.2·10⁶/q: exactly the y-arcs at level r₀) gives
  |S_{η_*}| ≤ (|η̂(δ)|/φ(q) + 1.3·10⁻⁷) y with |δ| ≥ 12245/q in the gap: ≤ 0.02 y.

Result (our corrected constants 0.8764, 3.8): Z ≤ 0.871 x²/κ at y = 10²⁵, decreasing in y,
vs the major arcs' 1.058259 (and vs [H]'s own 1.00948).  With r₂ = r₁ ≈ 10⁶ the same scheme
gives Z ≈ 1.11, so extending the levels is essential.

Usage: python3 scripts/minor_arc_y_scale_repair.py   (a few minutes)
"""
from mpmath import mp, mpf, log, sqrt, exp, euler, quad, pi
mp.dps = 15
EG = exp(euler); KAPPA = 49
phi = lambda w: w**2 * exp(-w**2 / 2)
PHI1 = sqrt(pi / 2)
def F(r): return EG * log(log(r)) + mpf('2.50637') / log(log(r))
def R(z, t): return mpf('0.27125') * log(1 + log(4*t) / (2*log(9*z**(mpf(1)/3) / (mpf('2.004')*t)))) + mpf('0.41415')
def L(t): return F(t/2) * (mpf(13)/4*log(t) + mpf('7.82')) + mpf('13.66')*log(t) + mpf('37.55')
def g1(z, r, c=mpf('0.8764'), c56=mpf('3.8')):
    """g_z(r) of (11.11)/GBound.lean: |S_{η₂}(α, z)| ≤ z g_z(r) (first case of Thm 3.1.1)."""
    return ((R(z, 2*r)*log(2*r) + c)*sqrt(F(r)) + mpf('2.5'))/sqrt(2*r) + L(2*r)/r + c56*z**(-mpf(1)/6)
def h(z):
    """second case of Thm 3.1.1, divided by z."""
    return mpf('0.276')*z**(-mpf(1)/6)*log(z)**mpf(1.5) + 1234*z**(-mpf(1)/3)*log(z)
def b(w, y, n):
    z = w*y
    if z < mpf('2.16e20'): return mpf(17)
    m = min(1, w)*n
    if m > z**(mpf(1)/3)/6: return h(z)
    if m < 670: return mpf(17)
    return max(g1(z, m), h(z))
def G(y, n):
    """|S_{η_*}(α, κy)| ≤ |φ|₁ G(y, n) y off 𝔐_{8,n}(y)."""
    pts = sorted(set(p for p in [mpf('1e-6'), mpf('2.16e20')/y, mpf(670)/n, 0.05, 0.2, 0.5, 1, 1.5,
                                 2, 3, 4, 6, 8, 12, 20] if p > 0))
    return quad(lambda w: b(w, y, n)*phi(w), pts)/PHI1
def Z(y, r2, cm=mpf('0.6394'), cp=mpf('2.0532'), JE=mpf('8.6297'), steps=30):
    x = KAPPA*y; r0 = mpf(150000)
    S = mpf('0.640209')*log(x) - mpf('0.021095')           # (14.30), /x
    D = log(sqrt(x)) + cm - log(7)                          # (12.42) with δ₀ = 392
    H = lambda r: (log(r+1) + cp)/D
    Q = sqrt(x/784)
    assert (20000*r2)**2 <= x/784 and 2*(r2+1) <= (2*Q)**mpf(0.6)
    lr = [log(r0) + (log(r2) - log(r0))*i/steps for i in range(steps+1)]
    gs = [G(y, exp(t)) for t in lr]
    assert all(gs[i+1] <= gs[i] for i in range(steps))     # g non-increasing (left sums = upper)
    base = gs[0]*(H(r0)*S - JE)
    mid = sum(gs[i]*(lr[i+1] - lr[i]) for i in range(steps))*S/D
    tail = gs[-1]*(1 - H(r2))*S
    M = base + mid + tail
    return M, (sqrt(PHI1*(M + mpf('3.5776e-4'))) + sqrt(mpf('1.0532e-11')))**2, (gs[0], gs[-1], base, mid, tail)
if __name__ == "__main__":
    for ly in [25, 26, 28, 32, 40, 80]:
        y = mpf(10)**ly; x = KAPPA*y; Q = sqrt(x/784)
        r2 = min((2*Q)**mpf(0.6)/2 - 1, Q/20000)
        M, z, parts = Z(y, r2)
        print(f"y=1e{ly}: r2={float(r2):.3g} g(r0)={float(parts[0]):.5f} g(r2)={float(parts[1]):.5f} "
              f"base={float(parts[2]):.4f} mid={float(parts[3]):.4f} tail={float(parts[4]):.4f} "
              f"M={float(M):.4f} Z={float(z):.4f}", flush=True)
    y = mpf(10)**25; M, z, _ = Z(y, mpf('1.04e6'))
    print(f"for comparison, y=1e25 with r2 = 1.04e6 (≈ [H]'s r₁): Z = {float(z):.4f}")
