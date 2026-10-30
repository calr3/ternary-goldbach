"""[B, Prop. 11.2.3]: the w-scaling of δ.

The proof of Prop. 11.2.3 writes S_{η_*}(α, x) = ∫ S_{η₂}(α, wx) φ(w) dw/w and applies
Theorem 3.1.1 to S_{η₂}(α, wx) with the same r = max(1, |δ|/8) q for every w.  But at scale
wx, 2α = a/q + δ_w/(wx) with δ_w = wδ, so the right parameter is r_w = max(1, w|δ|/8) q:
smaller than r for w < 1 (a *weaker* bound, since g is decreasing), larger for w > 1.
(For w > 1, Theorem 3.1.1's hypothesis |δ_w/wx| ≤ 1/(q Q_{wx}) also needs checking: it
holds for w ≤ ((4/3) x^{1/3} / (8r))^{3/2}, which is ≥ 94 for r ≤ r₁ = (3/8)x^{4/15}, x ≥ 10²⁵.)

For |δ| ≤ 8, r_w = q = r and nothing changes.  For |δ| > 8, r_w ≥ w r, so the honest integral
is A(r) = ∫ g_{wy,1}(w r) φ(w) dw, versus [B]'s C(r) = ∫ g_{wy,1}(r) φ(w) dw.  This script
checks A ≤ C (with our corrected constants 0.8103, 3.8), so [B]'s statement survives.
Result: A/C ≈ 0.87–0.89 for r₀ ≤ r ≤ r₁, y ∈ [10²⁵, 10¹⁰⁰].

Usage: python3 scripts/prop_11_2_3_check.py
"""
from mpmath import mp, mpf, log, sqrt, exp, euler, quad, inf, pi
mp.dps=20
EG=exp(euler)
def F(r): return EG*log(log(r))+mpf('2.50637')/log(log(r))
def R(z,t): return mpf('0.27125')*log(1+log(4*t)/(2*log(9*z**(mpf(1)/3)/(mpf('2.004')*t))))+mpf('0.41415')
def L(t): return F(t/2)*(mpf(13)/4*log(t)+mpf('7.82'))+mpf('13.66')*log(t)+mpf('37.55')
def g1(z,r,c=mpf('0.8103'),c56=mpf('3.8')):
    return ((R(z,2*r)*log(2*r)+c)*sqrt(F(r))+mpf('2.5'))/sqrt(2*r)+L(2*r)/r+c56*z**(-mpf(1)/6)
phi=lambda w: w**2*exp(-w**2/2)
for y in [mpf(10)**25, mpf(10)**40, mpf(10)**100]:
    K=log(y)/2; r1=mpf(3)/8*y**(mpf(4)/15)
    for r in [mpf(150000), mpf(10)**6, r1]:
        C=quad(lambda w: g1(w*y,r)*phi(w),[1/K,1,4,12,40])
        A=quad(lambda w: g1(w*y,w*r)*phi(w),[1/K,1,4,12,40])
        Alow=quad(lambda w: g1(w*y,w*r)*phi(w),[1/K,1]); Clow=quad(lambda w: g1(w*y,r)*phi(w),[1/K,1])
        print(f"y=1e{int(log(y,10))} r={float(r):.3g}: A/C = {float(A/C):.4f}  (w<1 part: A {float(Alow):.4g} vs C {float(Clow):.4g}; C/|phi|1 = {float(C/sqrt(pi/2)):.5g})")

print("--- g_{y,phi}(r) ~ C(r)/|phi|_1 at y = 1e25")
y=mpf(10)**25; K=log(y)/2
for r in [mpf(150000), mpf(300000), mpf(400000), mpf(3)/8*y**(mpf(4)/15)]:
    C=quad(lambda w: g1(w*y,r)*phi(w),[1/K,1,4,12,40])
    print(float(r), float(C/sqrt(pi/2)))
