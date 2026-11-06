# The Lean chain for (∫ G Φ⁺)/K_R, exactly as formalized in Explicit/WeilNumA.lean, WeilNumB.lean, WeilNumC.lean.
# Parameters m=2, ℓ=0.173, N=20, R=13, t0=2.39; grids: region A n_A equal steps on [0, R+t0],
# region B geometric u_k = t0 r^k (k ≤ n_B), region C closed form on [U1, 1/δ], region D Gaussian pieces.
import math
from fractions import Fraction as Fr
m, l, N, R, t0 = 2, 0.173, 20, 13, 2.39
r, nB, nA = 1.25, 20, 8
U1 = t0*r**nB
# K_R ≥ K0 = (2ℓ)^4 k0, k0 = 2∫_0^R (1 - ℓ²u²/6)^4 du
c = l*l/6
k0 = 2*(R - 4*c*R**3/3 + 6*c*c*R**5/5 - 4*c**3*R**7/7 + c**4*R**9/9)
K0 = (2*l)**4*k0
I0 = 2*2**(2*m)*R**(1-2*m)/(2*m-1)
I1 = 2*2**(2*m)*R**(1.5-2*m)/(2*m-1.5)
cN = 0.5*(math.log(N+0.25)-math.log(math.pi))
Off = 4**m*math.exp(m*l)*1e-15
p0 = 2*math.exp(m*l)/k0                         # P(t)/K0 = p0/max(1,ℓt)^4
beta = 0.5*math.log((N+0.25)/(N-0.75)) - 0.5*math.log(2*math.pi)
kap1 = (1 + I0/K0)/(2*math.pi)
kap0 = (beta + (cN*I0 + I1)/K0)/math.pi + Off/K0
kap0p = kap0 + kap1*math.log(R)                  # must be ≥ 0
def Pk(t): return p0/max(1, l*t)**4
def small(y): return (1/(2*y) + 1/(16*y*y))/math.pi
def regionA():
    h = (R+t0)/nA
    return sum(h/t0*(Pk(k*h) + kap1*(math.log((k+1)*h+R)-math.log(R)) + kap0p + small(k*h+R)) for k in range(nA))
def regionB():
    us = [t0*r**k for k in range(nB+1)]
    return sum(math.log(r)*(Pk(us[k]+R) + kap1*(math.log(us[k+1]+2*R)-math.log(R)) + kap0p + small(us[k]+2*R)) for k in range(nB))
c0 = kap0 + Pk(U1+R)
c2 = 2*R*kap1 + 1/(2*math.pi) + 1/(16*math.pi*U1)
def regionC(d):
    L, l1 = math.log(1/d), math.log(U1)
    return (kap1*L*L/2 + (c0 - 7*kap1/32)*L - 7*c0/32 + 15*kap1/128 - c0*l1 - kap1*l1*l1/2
            + (d*U1)**2*(c0 + kap1*l1)/4 + c2*(1/U1 + d/24))
vs = [1, 1.25, 1.5, 2, 3]
ex = lambda v: math.exp(-v*v/2)
Ep = sum((ex(vs[i])-ex(vs[i+1]))/vs[i]**2 for i in range(len(vs)-1)) + ex(3)/9
Fp = sum(math.log(vs[i+1])*(ex(vs[i])-ex(vs[i+1]))/vs[i]**2 for i in range(len(vs)-1)) + ex(3)/3
def regionD(d):
    L = math.log(1/d)
    return (c0 + kap1*L + c2*d)*Ep + kap1*Fp
def Jchain(d): return 2*(regionA() + regionB() + regionC(d) + regionD(d))
if __name__ == "__main__":
    print(f"k0={k0:.6f} K0={K0:.6e} I0/K0={I0/K0:.5f} I1/K0={I1/K0:.5f} p0={p0:.5f}")
    print(f"beta={beta:.5f} kap1={kap1:.6f} kap0={kap0:.5f} kap0'={kap0p:.5f} c0={c0:.5f} c2={c2:.4f} U1={U1:.3f}")
    print(f"E+={Ep:.5f} F+={Fp:.5f}; A={2*regionA():.4f} B={2*regionB():.4f}")
    import sys; sys.path.insert(0, 'scripts')
    from weil_model import J
    for d in [3e-4, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 3e-9]:
        jm = float(J(d, m=m, l=l, N=N, R=R))
        print(f"d={d:g}: chain={Jchain(d):.4f} model={jm:.4f} loss={Jchain(d)/jm-1:.2%}")
