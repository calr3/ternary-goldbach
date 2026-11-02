"""Generates TernaryGoldbach/Prelim/SmallMoebius.lean (|m(k)| <= sqrt(2/(k+1)) for k < 11815)."""
import os
from sympy import factorint
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
D = 10**12
TOP = 11814
def mu(n):
    f = factorint(n)
    if any(e > 1 for e in f.values()): return 0
    return -1 if len(f) % 2 else 1
def chk(k, P, Q): return (k+1)*(abs(P-Q) + k)**2 <= 2*10**24
P, Q = D, 0  # state at n = 1
bounds = [1] + list(range(1000, TOP+1, 1000)) + [TOP]
bounds = sorted(set(bounds))
states = {1: (P, Q)}; n = 1
for b in bounds[1:]:
    while n < b:
        m = mu(n+1)
        if m == 1: P += D//(n+1)
        elif m == -1: Q += D//(n+1)
        n += 1
        assert chk(n, P, Q), n
    states[n] = (P, Q)
walks = ""; cases = ""
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    walks += f"theorem w_{i} : walk {a} {states[a][0]} {states[a][1]} {b-a} = some ({states[b][0]}, {states[b][1]}) := by decide +kernel\n"
walks += f"\ntheorem s_1 : Pt 1 = {states[1][0]} ∧ Qt 1 = {states[1][1]} := by\n  constructor <;> simp [Pt, Qt] <;> norm_num\n"
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    walks += (f"theorem c_{i} : (Pt {b} = {states[b][0]} ∧ Qt {b} = {states[b][1]}) ∧ ∀ k, {a} < k → k ≤ {b} → chk k (Pt k) (Qt k) = true := by\n"
              f"  have h := w_{i}\n  rw [← s_{a}.1, ← s_{a}.2] at h\n"
              f"  obtain ⟨h1, h2⟩ := walk_spec {b-a} {a} _ (by norm_num) h\n"
              f"  simp only [Prod.mk.injEq] at h1\n"
              f"  exact ⟨⟨h1.1.symm, h1.2.symm⟩, fun k hk1 hk2 => h2 k hk1 (by omega)⟩\n"
              f"theorem s_{b} : Pt {b} = {states[b][0]} ∧ Qt {b} = {states[b][1]} := c_{i}.1\n")
for i in range(1, len(bounds)):
    a, b = bounds[i-1], bounds[i]
    if i < len(bounds) - 1:
        cases += f"  by_cases h{i} : k ≤ {b}\n  · exact bound_of_chk (c_{i}.2 k (by omega) h{i})\n"
    else:
        cases += f"  exact bound_of_chk (c_{i}.2 k (by omega) (by omega))\n"
src = open(os.path.join(HERE, "SmallMoebius.tmpl")).read().replace("@WALKS@", walks).replace("@CASES@", cases)
open(os.path.join(ROOT, "TernaryGoldbach/Prelim/SmallMoebius.lean"), "w").write(src)
print("max ratio", max(abs(sum(mu(n)/n for n in range(1,k+1)))*((k+1)/2)**0.5 for k in [2,3,10,100]))
