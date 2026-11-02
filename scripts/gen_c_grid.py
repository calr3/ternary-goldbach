"""Generates TernaryGoldbach/Prelim/SmallCGrid.lean.

Picks an adaptive grid 2.8 = a_0 < a_1 < ... < a_k = 80 (a_i = A_i/1000) and simulates the kernel
walk over u <= 3000 that accumulates, for every grid point, an upper bound for
E * sum_{u <= 3000} |mu(u)|/u^2 beta(a_i, u) (E = 10^15), with log u bounded above by the artanh walk.
"""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
D = 10**30; E = 10**15; K = 12; NU = 3000
def incrLo(n): return sum(2*D//((2*k+1)*(2*n+1)**(2*k+1)) for k in range(K))
def incrHi(n): return incrLo(n)+K+3*D//(25*(2*n+1)**25)+1
def sqf(v): return all(v % (d*d) != 0 for d in range(2, 56))
def cdiv(x, y): return (x + y - 1)//y
def c5(v): return cdiv(5*E, 3*v*v)
def bup(A, Lh, v):
    if 2000*Lh < A*D:
        return min(c5(v), cdiv(990*D*E, (A*D - 2000*Lh)*v*v))
    return c5(v)
Lhs = [0, 0]
for u in range(1, NU):
    Lhs.append(Lhs[-1] + incrHi(u))
def acc(A):
    return sum(bup(A, Lhs[v], v) for v in range(1, NU+1) if sqf(v))
def ok(A, B, a): return B*(18003*a + 10*E) <= 2800*18003*E
grid = []
A = 2800
while True:
    a = acc(A)
    if ok(A, 80000, a):
        grid.append((A, 80000, a)); break
    # largest B with ok
    B = (2800*18003*E)//(18003*a + 10*E)
    assert B > A, (A, B)
    B = A + max(1, (B - A)*99//100)
    assert ok(A, B, a)
    grid.append((A, B, a)); A = B
print(len(grid), "grid intervals:", [(g[0], g[1]) for g in grid])
GA = [g[0] for g in grid]
def L(xs): return "[" + ", ".join(str(x) for x in xs) + "]"
GT = "[" + ", ".join(f"({a}, {b}, {c})" for (a, b, c) in grid) + "]"
# walk states every 500 steps
def step(u, Lh, accs):
    Lh2 = Lh + incrHi(u)
    v = u + 1
    return Lh2, [x + (bup(A, Lh2, v) if sqf(v) else 0) for A, x in zip(GA, accs)]
bounds = [1] + list(range(500, NU+1, 500))
Lh = 0; accs = [bup(A, 0, 1) for A in GA]
states = {1: (Lh, accs)}; u = 1
for b in bounds[1:]:
    while u < b:
        Lh, accs = step(u, Lh, accs); u += 1
    states[u] = (Lh, list(accs))
assert states[NU][1] == [g[2] for g in grid]
def S(st): return "⟨" + str(st[0]) + ", " + L(st[1]) + "⟩"
walks = ""
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    walks += f"theorem wk_{i} : walkC {a} {b-a} {S(states[a])} = some {S(states[b])} := by decide +kernel\n"
walks += f"\ntheorem inv_1 : Inv 1 {S(states[1])} := Inv_one _ (by decide +kernel)\n"
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    walks += f"theorem inv_{b} : Inv {b} {S(states[b])} := walkC_spec {b-a} {a} _ _ (by norm_num) (by norm_num) inv_{a} wk_{i}\n"
# covering proof
cov = ""
for j, (A, B, a) in enumerate(grid):
    last = (j == len(grid) - 1)
    ind = "  " * (j + 1)
    tup = f"({A}, {B}, {a})"
    if not last:
        cov += f"{ind}rcases lt_or_ge y ({B} / 1000) with h{j} | h{j}\n"
        cov += f"{ind}· exact ⟨{tup}, by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩\n"
        cov += f"{ind}·\n"
    else:
        cov += f"{ind}exact ⟨{tup}, by simp [GT], by norm_num at *; linarith, by norm_num at *; linarith⟩\n"
src = open(os.path.join(HERE, "SmallCGrid.tmpl")).read()
src = (src.replace("@GA@", L(GA)).replace("@GT@", GT).replace("@WALKS@", walks)
       .replace("@COVER@", cov).replace("@NGRID@", str(len(grid)))
       .replace("@FINALACC@", L(states[NU][1])))
open(os.path.join(ROOT, "TernaryGoldbach/Prelim/SmallCGrid.lean"), "w").write(src)
