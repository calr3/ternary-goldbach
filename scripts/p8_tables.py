# P8d: certified tables for WeilNumC.lean. Mirrors ELpow/T12 (Prelim/SmallPsi.lean) exactly.
from fractions import Fraction as Q
from math import factorial, log, ceil, floor
def ELpow(a): return Q(27182818283**a, 10**(10*a))
def T12(f): return sum(f**i/factorial(i) for i in range(12))
def EHpow(a): return Q(27182818286**a, 10**(10*a))
def T12up(f): return T12(f) + f**12*Q(13, factorial(12)*12)
def logup(x, prec=10**6):
    """(a, f) with x ≤ ELpow a * T12 f, a + f ≈ log x rounded up."""
    y = Q(ceil(log(x)*prec) + 1, prec)
    a = floor(y); f = y - a
    while not x <= ELpow(a)*T12(f):
        f += Q(1, prec)
        if f >= 1: a += 1; f -= 1
    return a, f
def loglo(x, prec=10**6):
    y = Q(floor(log(x)*prec) - 1, prec)
    a = floor(y); f = y - a
    while not EHpow(a)*T12up(f) <= x:
        f -= Q(1, prec)
        if f < 0: a -= 1; f += 1
    return a, f
l, R, r = Q(173, 1000), 13, Q(5, 4)
P0, K1, K0 = Q(24567, 100000), Q(16385, 100000), Q(-23516, 100000)
PIlo = Q(3141592, 10**6)
h = Q(1539, 800)
def smallU(y): return (1/(2*y) + 1/(16*y*y))/PIlo
def termA(k, y):
    a = k*h
    return (P0/max(Q(1), l*a)**4 + K1*y + K0 + smallU(a + R))/Q(239, 100)*h
LR = logup(r)
def termB(k, y):
    a = R + Q(239, 100)*r**k
    return (P0/max(Q(1), l*a)**4 + K1*y + K0 + smallU(a + R))*(LR[0] + LR[1])
tabA = [logup((k+1)*h + R) for k in range(8)]
tabB = [logup(R + Q(239, 100)*r**(k+1) + R) for k in range(20)]
SA = sum(termA(k, a + f) for k, (a, f) in enumerate(tabA))
SB = sum(termB(k, a + f) for k, (a, f) in enumerate(tabB))
print("LR =", LR, float(LR[0]+LR[1]))
print("tabA =", tabA)
print("tabB =", tabB)
print("SA =", float(SA), "SB =", float(SB))

# exp(q) two-sided: lower ELpow a * T12 f, upper EHpow a * T12up f  (q = a + f)
def expq(q):
    a = floor(q); f = q - a
    return ELpow(a)*T12(f), EHpow(a)*T12up(f)
for q in [Q(1,2), Q(25,32), Q(9,8), Q(2), Q(9,2), Q(173,500)]:
    lo, hi = expq(q)
    print("exp", q, float(lo), float(hi), "exp(-q) in", float(1/hi), float(1/lo))
for x in [Q(3,2), Q(3), Q(81,77), Q(81,4)]:
    print("logup", x, logup(x))
U = Q(239,100)*r**20
for x in [Q(13), Q(3141592, 10**6), U]:
    print("loglo", x, loglo(x))
print("logup U", logup(U))

# rational atom bounds used in WeilNumC
eU = {Q(1,2): Q(60653066,10**8), Q(25,32): Q(45783337,10**8), Q(9,8): Q(32465247,10**8), Q(2): Q(13533529,10**8), Q(9,2): Q(1110900,10**8)}
eL = {Q(25,32): Q(45783336,10**8), Q(9,8): Q(32465246,10**8), Q(2): Q(13533528,10**8), Q(9,2): Q(1110899,10**8)}
for q in eU: assert 1 <= eU[q]*expq(q)[0], q
for q in eL: assert eL[q]*expq(q)[1] <= 1, q
Ep = eU[Q(1,2)] - eL[Q(25,32)] + (eU[Q(25,32)] - eL[Q(9,8)])/Q(25,16) + (eU[Q(9,8)] - eL[Q(2)])/Q(9,4) + (eU[Q(2)] - eL[Q(9,2)])/4 + eU[Q(9,2)]/9
# E = e1 - e2 + (e2 - e3)/(25/16) + ...: as a combination, coefficients of e2..e5 negative: use lower bounds
Ep = eU[Q(1,2)] + eU[Q(25,32)]*0 - eL[Q(25,32)]*(1 - Q(16,25)) - eL[Q(9,8)]*(Q(16,25) - Q(4,9)) - eL[Q(2)]*(Q(4,9) - Q(1,4)) - eL[Q(9,2)]*(Q(1,4) - Q(1,9))
LR, L32, L2, L3 = Q(223145,10**6), Q(405467,10**6), Q(6931471808,10**10), Q(1098614,10**6)
Fp = LR*(eU[Q(1,2)] - eL[Q(25,32)]) + L32*(eU[Q(25,32)] - eL[Q(9,8)])/Q(25,16) + L2*(eU[Q(9,8)] - eL[Q(2)])/Q(9,4) + L3*(eU[Q(2)] - eL[Q(9,2)])/4 + eU[Q(9,2)]/3
print("E+ =", float(Ep), "F+ =", float(Fp))
U = Q(239,100)*r**20
c0 = K0 + P0/max(Q(1), l*(U+R))**4
l1lo, l1hi = Q(5334163,10**6), Q(5334166,10**6)
PIhi = Q(3141593,10**6)
c2hi = 2*R*K1 + 1/(2*PIlo) + 1/(16*PIlo*U)
A, B = Q(26618,10**4), Q(198,100)
q2 = K1
q1 = 2*(c0 - 7*K1/32 + K1*Ep)
q0 = 2*(A + B - 7*c0/32 + 15*K1/128 - c0*l1hi - K1*l1lo**2/2 + c2hi/U + c0*Ep + K1*Fp)
X2 = c0/2 + K1*(l1hi/2 - Q(1,4))
q3 = U*X2
print("c0 =", float(c0), c0 < 0, "c2hi =", float(c2hi))
print("q2, q1, q0, q3 =", float(q2), float(q1), float(q0), float(q3))
print("delta-term coeff -35/24+1/2+E+ =", float(-Q(35,24)+Q(1,2)+Ep))
import math
for d in [3e-4, 1e-6, 3e-9]:
    L = math.log(1/d); print(d, float(q2)*L*L + float(q1)*L + float(q0) + float(q3)*d)
