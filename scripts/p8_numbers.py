# P8d: the constants of WeilNumC.lean (ℓ = 0.173, N = 20, R = 13, r = 5/4, n_A = 8, n_B = 20).
from fractions import Fraction as Q
from mpmath import mp, mpf, log, exp, pi, sqrt
mp.dps = 40
l, N, R, r, nA, nB = Q(173, 1000), 20, 13, Q(5, 4), 8, 20
c = l*l/6
kB = 2*(R - 4*c*R**3/3 + 6*c**2*R**5/5 - 4*c**3*R**7/7 + c**4*R**9/9)
K0 = (2*l)**4*kB
I0 = Q(32, 3*R**3)
print("kB =", float(kB), "K0 =", float(K0), "I0 =", float(I0))
p0 = 2*exp(mpf(2*l.numerator)/l.denominator)/mpf(kB.numerator)*kB.denominator
kap1 = (1 + mpf(I0.numerator)/I0.denominator/(mpf(K0.numerator)/K0.denominator))/(2*pi)
I1 = mpf('12.8')*mpf(13)**mpf('-2.5')
cN = 0.5*(log(mpf('20.25')) - log(pi))
Off = 16*exp(mpf('0.346'))*mpf('1e-15')
K0f = mpf(K0.numerator)/K0.denominator
kap0 = (1/pi)*(-0.5*log(2*pi) + 0.5*log(mpf(81)/77) + (cN*mpf(I0.numerator)/I0.denominator + I1)/K0f) + Off/K0f
print("p0 =", p0, "kap1 =", kap1, "kap0 =", kap0)

P0, K1, K0c = Q(24567, 100000), Q(16385, 100000), Q(-23516, 100000)
assert float(P0) >= p0 and float(K1) >= kap1 and float(K0c) >= kap0
def M(x): return mpf(x.numerator)/x.denominator if isinstance(x, Q) else mpf(x)
def smallT(y): return (1/pi)*(1/(2*M(y)) + 1/(16*M(y)**2))
def PsiBar(a, b): return M(P0)/max(1, M(l)*M(a))**4 + M(K1)*log(M(b)+R) + M(K0c) + smallT(M(a)+R)
h = (R + Q(239, 100))/nA
A = sum(PsiBar(k*h, (k+1)*h)/mpf('2.39')*M(h) for k in range(nA))
B = sum(PsiBar(R + Q(239,100)*r**k, R + Q(239,100)*r**(k+1))*log(M(r)) for k in range(nB))
U = Q(239, 100)*r**nB
l1 = log(M(U))
c0 = M(K0c) + M(P0)/max(1, M(l)*(M(U)+R))**4
c2 = 2*R*M(K1) + 1/(2*pi) + 1/(16*pi*M(U))
ex = lambda q: exp(-mpf(q))
E = (ex(0.5)-ex(25/32))/1 + (ex(25/32)-ex(9/8))/(25/16) + (ex(9/8)-ex(2))/(9/4) + (ex(2)-ex(4.5))/4 + ex(4.5)/9
F = log(1.25)*(ex(0.5)-ex(25/32)) + log(1.5)*(ex(25/32)-ex(9/8))/(25/16) + log(2)*(ex(9/8)-ex(2))/(9/4) + log(3)*(ex(2)-ex(4.5))/4 + ex(4.5)/3
X2 = c0/2 + M(K1)*(l1/2 - 0.25)
X4 = c0/4 + M(K1)*(l1/4 - 1/16)
q2 = M(K1)
q1 = 2*(c0 - 7*M(K1)/32 + M(K1)*E)
q0 = 2*(A + B - 7*c0/32 + 15*M(K1)/128 - c0*l1 - M(K1)*l1**2/2 + c2/M(U) + c0*E + M(K1)*F)
q3 = 2*(M(U)*X2/2)
print("A =", A, "B =", B, "U =", float(U), "logU =", l1)
print("c0 =", c0, "c2 =", c2, "E =", E, "F =", F, "X2 =", X2, "X4 =", X4)
print("JW(δ) = q2 L² + q1 L + q0 + q3 δ:", float(q2), float(q1), float(q0), float(q3))
print("check c2/2 - 35c2/24 + c2 E < 0:", float(c2*(0.5 - 35/24 + E)))
import math
for d in [3e-4, 1e-4, 1e-6, 3e-9]:
    L = math.log(1/d)
    print(d, float(q2*L*L + q1*L + q0 + q3*d))
