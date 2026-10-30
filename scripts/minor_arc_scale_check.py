"""[B, Thm 13.2.1]: the scale of the major arcs in the ℓ∞ input.

Prop 13.1.2 needs, for one family of arcs 𝔐_{8,r}, both an ℓ² bound H(r) for S_{η₊} and an
ℓ∞ bound |S_{η_*}(α, x)| ≤ g(r) off 𝔐_{8,r}.  In Thm 13.2.1:

* H(r) comes from Cor 12.2.5 / (12.42) with arcs at scale x (c⁻ = 0.6394 = log(1/√(2·8)) +
  log 2 + 1.3325822 uses Q = √(x/16)); J (14.7) and the major arcs (14.27), (14.17) are at scale x;
* the ℓ∞ bound (13.14)–(13.17) is derived only for α outside the arcs at scale y = x/κ
  ("y is used instead of x to define 𝔐_{8,r}", p. 249; same in arXiv:1312.7748, p. 48).

The y-arcs are κ = 49 times wider.  For α outside the x-arcs but inside the y-arcs, Theorem 3.1.1
at scale y only gives r_α = max(q, |δ_y| q/8) ≥ max(q, r/κ).

This script quantifies two repairs:
1. everything at scale y: c⁻ → c⁻ − log 7 (and the major arcs would have to be 𝔐_{392,r₀} at
   scale x, beyond the range |δ| ≤ 600000 gcd(q,2)/q of Thm 7.1.4);
2. everything at scale x, using Cor 7.1.3 (GRH-verified, q ≤ 300000) on the gap region: fails for
   levels r > 300000 with q ∈ (300000, r], where only g(q) ≥ g(300000) is available; the tail
   term (14.43) then grows by the factor g(3·10⁵)/g(r₁).
"""
from mpmath import mp, mpf, log, sqrt, pi
mp.dps=20
x=mpf('4.9e26'); kappa=49; y=x/kappa; r0=150000; cp=mpf('2.0532')
S=mpf('0.640209')*log(x)-mpf('0.021095')   # S/x
JE=mpf('8.6297')
def parts(cm, g0, g1int, g1):
    a = g0*((log(r0+1)+cp)/(log(sqrt(x))+cm)*S - JE)
    b = 2*S/(log(x)+2*cm)*g1int
    r1=mpf(3)/8*y**(mpf(4)/15)
    jump = 1-(log(r1+1)+cp)/(log(sqrt(x))+cm)
    c = jump*g1*S
    return a,b,c
# corrected g values from scripts/minor_arc_total_numerics.py: g(r0)=0.042939; ∫g/r = f0+f1+f2
g0=mpf('0.042939'); gint=mpf('0.071498')+mpf('0.0195646')+mpf('0.0011110')
# g(r1) at y: (14.43) value 0.311811 = 7/15*g1*S  -> g1
g1=mpf('0.311811')/(mpf(7)/15*S)
for name,cm in [('x-arcs (book c-)',mpf('0.6394')),('y-arcs (c- - log 7)',mpf('0.6394')-log(7))]:
    a,b,c=parts(cm,g0,gint,g1)
    M=a+b+c
    Z=(sqrt(sqrt(pi/2)*(M+mpf('3.5776e-4')))+sqrt(mpf('1.0532e-11')))**2
    print(name, 'M parts',[float(t) for t in (a,b,c)],'M',float(M),'Z',float(Z))

# repair 2: the tail term (14.43) with g(r1) replaced by g(3e5) (values of g_{y,φ} at y = 1e25
# from scripts/prop_11_2_3_check.py: g(3e5) ≈ 0.031740, g(r1) ≈ 0.015559)
tail = mpf('0.311811') * mpf('0.031740') / mpf('0.015559')
print('repair 2: (14.43) tail', float(tail), 'instead of 0.311811; M grows by', float(tail - mpf('0.311811')))
