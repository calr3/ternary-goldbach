# Generator/validator for the base checks of Prop 12.2.4 with c+ = 2 (exact rationals).
from fractions import Fraction as Fr
import math, itertools, sys
PR = [2,3,5,7,11,13]
D = 10**12
N = 2600
def f1p(p):
    u = p**(1/3); return (1+1/u**2)/(1+(u+u*u)/(p*(p-1)))
def up(x, d=6): return Fr(math.ceil(x*10**d), 10**d)
def dn(x, d=6): return Fr(math.floor(x*10**d), 10**d)
fup = {p: up(f1p(p), 5) for p in PR}
# lower bounds for 0.6586 log p/p + 0.3414 log p and for 0.3414 (log p - log p/p)
wl = {p: dn(0.6586*math.log(p)/p + 0.3414*math.log(p), 6) - Fr(1,10**6) for p in PR}
rl = {p: dn(0.3414*(math.log(p) - math.log(p)/p), 6) - Fr(1,10**6) for p in PR}
L2 = Fr(693147, 10**6)
# blocks
blocks = []; a = 4
while a < N:
    b = min(N - 1, max(a, int(a*1.07)))
    j = math.floor(6*math.log2(a))
    while 2**j > a**6: j -= 1
    v = dn(a**(1/3), 3)
    while v**3 > a: v -= Fr(1,1000)
    blocks.append((a, b, j, v)); a = b + 1
# phi, squarefree
phi = list(range(N+1)); sq = [True]*(N+1)
for i in range(2, N+1):
    if phi[i] == i:
        for k in range(i, N+1, i): phi[k] -= phi[k]//i
        for k in range(i*i, N+1, i*i): sq[k] = False
worst = None
for k in range(7):
    for T in itertools.combinations(PR, k):
        A = math.prod(T)
        K = math.prod(Fr(p, p-1) for p in T); F = math.prod(fup[p] for p in T)
        W = sum((wl[p] for p in T), Fr(0)); c = Fr(1768, 10000)*K*F
        acc = 0; bi = 0
        for r in range(1, N):
            if math.gcd(r, A) == 1 and sq[r]: acc += -(-D // phi[r])
            while bi < len(blocks) and blocks[bi][1] == r:
                a_, b_, j_, v_ = blocks[bi]
                lhs = K*Fr(acc, D) + c/v_; rhs = j_*L2/6 + Fr(19999999, 10**7) + W
                m = rhs - lhs
                if worst is None or m < worst[0]: worst = (m, A, a_)
                bi += 1
        # Ramare tail: n >= 2600, v = 13.75 (13.75^3 <= 2600)
        R = sum((rl[p] for p in T), Fr(0))
        mt = Fr(1375,100)*(R + Fr(6674176, 10**7)) - Fr(74608, 10000)*K*F
        if mt <= 0: print("Ramare tail FAILS for", A, float(mt))
print("blocks", len(blocks), "worst block margin", float(worst[0]), "at A", worst[1], "a", worst[2])

def lean_blocks():
    out = []
    for (a, b, j, v) in blocks:
        out.append(f"({a}, {b}, {j}, ({v.numerator} : ℚ) / {v.denominator})")
    return "[" + ",\n  ".join(out) + "]"
if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "lean":
    print(lean_blocks())
