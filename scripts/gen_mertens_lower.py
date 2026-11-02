"""Generates TernaryGoldbach/Prelim/SmallMertensLower.lean.

Simulates the kernel walk (D = 10^30) over n <= 10002 for log n, sum_{m<=n} Lambda(m)/m and psi(n),
checking (2.13) at every 3 <= N <= 10^4, and writes the checkpoint states.
"""
import os
from sympy import primerange
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
D = 10**30
K = 12
def incrLo(n): return sum(2*D//((2*k+1)*(2*n+1)**(2*k+1)) for k in range(K))
def incrHi(n): return incrLo(n)+K+3*D//(25*(2*n+1)**25)+1
def isPr(p): return p >= 2 and all(p < d*d or p % d != 0 for d in range(2, 148))
TOP = 10002
PPL = [(p**k, p, k) for p in primerange(2, 101) for k in range(2, 14) if p**k <= TOP]
PPL.sort()
ppd = {m: (p, k) for (m, p, k) in PPL}
K32 = incrLo(2) + 346573590150000000000000000000
def lamB(m, Lo, Hi):
    if isPr(m): return (Lo, Hi)
    if m in ppd:
        k = ppd[m][1]; return (Lo//k, Hi//k + 1)
    return (0, 0)
def step(n, s):
    Llo, Lhi, Slo, Shi, Plo, Phi = s
    L1, L2 = Llo + incrLo(n), Lhi + incrHi(n)
    assert n < 3 or L2 <= Slo + K32, n
    lo, hi = lamB(n+1, L1, L2)
    return (L1, L2, Slo + lo//(n+1), Shi + hi//(n+1) + 1, Plo + lo, Phi + hi)
s = (0, 0, 0, 0, 0, 0)
bounds = [1] + list(range(1000, 10001, 1000)) + [TOP]
states = {1: s}; n = 1
for b in bounds[1:]:
    while n < b:
        s = step(n, s); n += 1
    states[n] = s
def S(v): return "⟨" + ", ".join(str(x) for x in v) + "⟩"
# point value check
from fractions import Fraction as Fr
s4 = states[10000]; s2 = states[TOP]
val = Fr(s4[2], D) - Fr(s4[5], D) / 10001 - Fr(s2[1], D)
print("point value lower bound", float(val))
assert val >= Fr(-1578, 1000)
ppl_src = "[" + ", ".join(f"({m}, {p}, {k})" for (m, p, k) in PPL) + "]"
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "SmallMertensLower.tmpl")).read()
src = src.replace("@PPL@", ppl_src).replace("@K32@", str(K32)).replace("@INCRLO2@", str(incrLo(2)))
walks = ""
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    walks += f"theorem wk_{i} : walkM {a} {b-a} {S(states[a])} = some {S(states[b])} := by decide +kernel\n"
walks += "\ntheorem inv_1 : Inv 1 " + S(states[1]) + " := Inv_one\n"
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    walks += f"theorem inv_{b} : Inv {b} {S(states[b])} := walkM_spec {b-a} {a} _ _ (by norm_num) (by norm_num) inv_{a} wk_{i}\n"
src = src.replace("@WALKS@", walks)
open(os.path.join(ROOT, "TernaryGoldbach/Prelim/SmallMertensLower.lean"), "w").write(src)
print(len(PPL), "prime powers; K32 =", K32)
