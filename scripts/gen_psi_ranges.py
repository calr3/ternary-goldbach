# P9b: generate Explicit/PsiRanges.lean: |ψ(x) − x| ≤ c√x on [X, X'] for half-decades in [1e6, 1e17].
import math, sys
from fractions import Fraction as Q
sys.path.insert(0, 'scripts')
from p8_tables import ELpow, T12, EHpow, T12up
import p8_psi_model as M

def up_dec(x, k=6):
    """decimal ≥ x with k significant digits"""
    x = Q(x)
    e = math.floor(math.log10(float(x))) - k + 1
    s = Q(10)**e
    return Q(math.ceil(x/s))*s
def lo_dec(x, k=6):
    x = Q(x)
    e = math.floor(math.log10(float(x))) - k + 1
    s = Q(10)**e
    return Q(math.floor(x/s))*s
def logup(x, prec=10**6):
    y = Q(math.ceil(math.log(float(x))*prec) + 1, prec)
    a = math.floor(y); f = y - a
    while not x <= ELpow(a)*T12(f):
        f += Q(1, prec)
        if f >= 1: a += 1; f -= 1
    return a, f
def expup(f):       # e^f ≤ T12up(f), 0 ≤ f ≤ 1
    return up_dec(T12up(f), 9)
def expneg_up(y):   # e^{-y} ≤ u with 1 ≤ u*ELpow a*T12 f
    a = math.floor(y); f = y - a
    u = up_dec(1/(ELpow(a)*T12(f)), 6)
    assert 1 <= u*ELpow(a)*T12(f)
    return a, f, u
def lean_q(q):
    q = Q(q)
    return f"({q.numerator} / {q.denominator} : ℝ)" if q.denominator != 1 else f"({q.numerator} : ℝ)"
def sqrt_up(z):  # rational w ≥ √z
    w = up_dec(Q(math.sqrt(float(z))), 7)
    while w*w < z: w += Q(1, 10**7)
    return w
def sqrt_lo(z):
    w = lo_dec(Q(math.sqrt(float(z))), 7)
    while w*w > z: w -= w/10**7
    return w

NEWCALLS = '''  have hKe : Real.exp ({K} * (1 / {D} : ℝ)) ≤ {E1} :=
    (Real.exp_le_exp.2 (show {K} * (1 / {D} : ℝ) ≤ {F1} by norm_num)).trans hE1
  have hup := psi_range_up (δ := 1 / {D}) (K := {K}) (y0 := {Y}) (X := {X0}) (X' := {X1}) (c := {C})
    (LU := {LU}) (E1 := {E1}) (E8 := {E8}) (Eh := {Eh}) (q := {Qv}) (sY := {SY}) (sYX := {SYX})
    (rX := {RX}) (rX' := {RX1})
    (hδ0 := by norm_num) (hδ1 := by norm_num) (hK := by norm_num) (hKδ := by norm_num) (hy0 := by norm_num)
    (hX1 := by norm_num) (hYX := by nlinarith) (hLU := hLU) (hE1 := by convert hE1 using 2; norm_num)
    (hE8 := by convert hE8 using 2; norm_num) (hEh := by convert hEh using 2; norm_num)
    (hq := by have h := hq; norm_num at h ⊢; linarith) (hq1 := by norm_num) (hsY := hsY) (hsYX := hsYX)
    (hrX0 := by norm_num) (hrX := hrX) (hrX' := hrX') (hc := by norm_num) hx1 hx2
  have hlo := psi_range_lo (δ := 1 / {D}) (K := {K}) (y0 := {Y}) (X := {X0}) (X' := {X1}) (c := {C})
    (LU := {LU}) (E8 := {E8}) (Eh := {Eh}) (q := {Qv}) (sY := {SY}) (sYX := {SYX})
    (rX := {RX}) (rX' := {RX1})
    (hδ0 := by norm_num) (hδ1 := by norm_num) (hKδ0 := by norm_num) (hKδ := by norm_num) (hy0 := by norm_num)
    (hX1 := by norm_num) (hYX := by nlinarith) (hLU := hLU)
    (hE8 := by convert hE8 using 2; norm_num) (hEh := by convert hEh using 2; norm_num)
    (hq := by have h := hq; norm_num at h ⊢; linarith) (hsY := hsY) (hsYX := hsYX)
    (hrX0 := by norm_num) (hrX := hrX) (hrX' := hrX') (hc := by norm_num) hx1 hx2
'''
ranges = []
X = Q(10**6)
bounds = [Q(10**6)]
k = 6
while bounds[-1] < 10**17:
    b = bounds[-1]
    nb = b*Q(32, 10) if str(b.numerator)[0] == '1' else b*Q(10, 32)*10
    bounds.append(min(nb, Q(10**17)))
out = []
summary = []
for i in range(len(bounds) - 1):
    X0, X1 = bounds[i], bounds[i+1]
    # parameters from the model
    best = None
    for kk in range(17, 77):
        d = 10**(-kk/8)
        if not (3e-9 <= d <= 1/208): continue
        for K in [3.5 + 0.1*j for j in range(40)]:
            for jj in range(0, 60):
                y0 = 10**(jj/4)
                if y0*math.exp(K*d) > float(X0): break
                c = M.sep_c(float(X0), float(X1), d, K, y0)
                if best is None or c < best[0]: best = (c, d, K, y0)
    c_m, d, K, y0 = best
    D = round(1/d); delta = Q(1, D); Kq = Q(round(K*10), 10); y0q = Q(round(y0))
    a, f = logup(Q(D)); LU = a + f
    E1 = expup(delta**2/2 + Kq*delta); E8 = expup(delta**2/8); Eh = expup(Kq*delta/2)
    qa, qf, qu = expneg_up(Kq**2/2); q = 2*qu
    sY = sqrt_up(y0q/X0); sYX = up_dec(1/sqrt_lo(y0q*X0), 7)
    rX = sqrt_lo(X0); rX1 = sqrt_up(X1)
    JWu = Q(16385, 100000)*LU**2 - Q(4271, 10000)*LU + Q(72032, 10000) + Q(5773, 100)*delta + Q(1, 10**6)
    Lb = E8*(Eh + sY)*JWu
    cu = (E1/(1-q) - 1)*rX1 + Lb/(1-q) + Q(1, 10**11)*rX1/(1-q) + 4*y0q*E1/rX + Q(2533, 10)*E8/delta/(1-q)*(1/X0 + sYX)
    cl = (Kq*delta + 2*q)*rX1 + 2*y0q/rX + Lb + Q(1, 10**11)*rX1 + Q(2533, 10)*E8/delta*(Eh/X0 + sYX)
    c = up_dec(max(cu, cl), 4)
    assert y0q*E1 <= X0
    summary.append((float(X0), float(X1), float(c), D, float(Kq), int(y0q)))
    name = f"psi_range_{i}"
    calls = NEWCALLS.format(K=lean_q(Kq), D=D, Y=lean_q(y0q), X0=lean_q(X0), X1=lean_q(X1), C=lean_q(c), LU=lean_q(LU), F1=lean_q(delta**2/2 + Kq*delta),
        E1=lean_q(E1), E8=lean_q(E8), Eh=lean_q(Eh), Qv=lean_q(q), SY=lean_q(sY), SYX=lean_q(sYX), RX=lean_q(rX), RX1=lean_q(rX1))
    out.append(f"""
/-- `|ψ(x) − x| ≤ {float(c)} √x` for `{float(X0):.4g} ≤ x ≤ {float(X1):.4g}` (`δ = 1/{D}`, `K = {float(Kq)}`, `y₀ = {int(y0q)}`). -/
theorem {name} {{x : ℝ}} (hx1 : {lean_q(X0)} ≤ x) (hx2 : x ≤ {lean_q(X1)}) :
    |psiR x - x| ≤ {lean_q(c)} * √x := by
  have hLU : Real.log (1 / (1 / {D} : ℝ)) ≤ {lean_q(LU)} := by
    have := log_le_cert (x := 1 / (1 / {D} : ℝ)) ({D} : ℚ) (by norm_num) (by norm_num) {a} ({f.numerator} / {f.denominator})
      (by norm_num) (by decide +kernel)
    norm_num at this ⊢; linarith
  have hE1 := exp_le_rat (f := {lean_q(delta**2/2 + Kq*delta).replace(': ℝ', ': ℚ')}) (u := {lean_q(E1).replace(': ℝ', ': ℚ')}) (by norm_num) (by norm_num) (by decide +kernel)
  have hE8 := exp_le_rat (f := {lean_q(delta**2/8).replace(': ℝ', ': ℚ')}) (u := {lean_q(E8).replace(': ℝ', ': ℚ')}) (by norm_num) (by norm_num) (by decide +kernel)
  have hEh := exp_le_rat (f := {lean_q(Kq*delta/2).replace(': ℝ', ': ℚ')}) (u := {lean_q(Eh).replace(': ℝ', ': ℚ')}) (by norm_num) (by norm_num) (by decide +kernel)
  have hq := exp_neg_le_cert {qa} ({qf.numerator} / {qf.denominator}) ({qu.numerator} / {qu.denominator}) (by norm_num) (by decide +kernel)
  have hsY := sqrt_le_rat (z := {lean_q(y0q)} / {lean_q(X0)}) (w := {lean_q(sY)}) (by norm_num) (by norm_num)
  have hsYX := inv_sqrt_le_rat (z := {lean_q(y0q)} * {lean_q(X0)}) (w := {lean_q(sYX)}) (by norm_num) (by norm_num)
  have hrX := le_sqrt_rat (z := {lean_q(X0)}) (w := {lean_q(rX)}) (by norm_num) (by norm_num)
  have hrX' := sqrt_le_rat (z := {lean_q(X1)}) (w := {lean_q(rX1)}) (by norm_num) (by norm_num)
  push_cast at hE1 hE8 hEh hq
{calls}  rw [abs_le]; constructor <;> linarith
""")
hdr = '''import TernaryGoldbach.Explicit.PsiRange
import TernaryGoldbach.Explicit.WeilNumC

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# `|ψ(x) − x| ≤ c √x` on half-decades of `[10⁶, 10¹⁷]` (route D, step P9b)

Generated by `scripts/gen_psi_ranges.py`: one `(δ, K, y₀)` per range, atoms certified by the
kernel (`decide +kernel`), and `psi_range_up` / `psi_range_lo`.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology
open TernaryGoldbach.Prelim.Small (T12 ELpow EHpow T12up exp_le_T12up)

namespace TernaryGoldbach.Explicit

omit [Fact TernaryGoldbach.RHUpTo] in
theorem exp_le_rat {f u : ℚ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (h : T12up f ≤ u) : Real.exp (f : ℝ) ≤ (u : ℝ) := by
  have h1 := exp_le_T12up hf0 hf1
  have h2 : ((T12up f : ℚ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast h
  exact h1.trans h2

omit [Fact TernaryGoldbach.RHUpTo] in
theorem sqrt_le_rat {z w : ℝ} (hw : 0 ≤ w) (h : z ≤ w ^ 2) : √z ≤ w := by
  rw [show w = √(w ^ 2) from (Real.sqrt_sq hw).symm]; exact Real.sqrt_le_sqrt h

omit [Fact TernaryGoldbach.RHUpTo] in
theorem le_sqrt_rat {z w : ℝ} (hw : 0 ≤ w) (h : w ^ 2 ≤ z) : w ≤ √z := Real.le_sqrt_of_sq_le h

omit [Fact TernaryGoldbach.RHUpTo] in
theorem inv_sqrt_le_rat {z w : ℝ} (hw : 0 < w) (h : 1 ≤ w ^ 2 * z) : 1 / √z ≤ w := by
  have hz : 0 < z := by
    by_contra hz; push Not at hz; nlinarith [sq_nonneg w]
  have h1 : 1 / w ≤ √z := Real.le_sqrt_of_sq_le (by rw [div_pow, one_pow, div_le_iff₀ (by positivity)]; linarith)
  rw [div_le_iff₀ (Real.sqrt_pos.2 hz)]
  rw [div_le_iff₀ hw] at h1; linarith
'''
with open('TernaryGoldbach/Explicit/PsiRanges.lean', 'w') as fh:
    fh.write(hdr + "".join(out) + "\nend TernaryGoldbach.Explicit\n")
for row in summary: print(row)

# combined statement
def lq(q): return lean_q(q)
cs = [Q(row[2]).limit_denominator(100) for row in summary]
# recompute exact c values as emitted
import re
txt = open('TernaryGoldbach/Explicit/PsiRanges.lean').read()
cvals = re.findall(r"\|psiR x - x\| ≤ \((\d+) / (\d+) : ℝ\) \* √x", txt)
cvals = [Q(int(a), int(b)) for a, b in cvals]
n = len(bounds) - 1
defn = "noncomputable def cW (x : ℝ) : ℝ :=\n  " + "".join(
    f"if x ≤ {lq(bounds[i+1])} then {lq(cvals[i])} else " for i in range(n - 1)) + lq(cvals[n-1])
proof = ["theorem psi_mid {x : ℝ} (h1 : 1e6 ≤ x) (h2 : x ≤ 1e17) : |psiR x - x| ≤ cW x * √x := by",
         "  unfold cW"]
for i in range(n - 1):
    proof.append(f"  by_cases h{i} : x ≤ {lq(bounds[i+1])}")
    lo = "(by norm_num at h1 ⊢; linarith)" if i == 0 else f"(by push Not at h{i-1}; linarith)"
    proof.append(f"  · rw [if_pos h{i}]; exact psi_range_{i} {lo} h{i}")
    proof.append(f"  rw [if_neg h{i}]")
proof.append(f"  push Not at h{n-2}")
proof.append(f"  exact psi_range_{n-1} h{n-2}.le (by norm_num at h2 ⊢; linarith)")
def chain(name, stmt, bound, upto):
    lines = [f"theorem {name} {stmt} := by", "  unfold cW"]
    for i in range(n - 1):
        if i < upto:
            lines.append(f"  by_cases h{i} : x ≤ {lq(bounds[i+1])}")
            lines.append(f"  · rw [if_pos h{i}]; norm_num")
            lines.append(f"  rw [if_neg h{i}]")
        else:
            lines.append(f"  exfalso; push Not at h{i-1}; norm_num at hx; linarith")
            return "\n".join(lines)
    lines.append("  norm_num")
    return "\n".join(lines)
def chain_lo(name, stmt, start, upto):
    """cW x ≤ bound for bounds[start] < x ≤ bounds[upto]."""
    lines = [f"theorem {name} {stmt} := by", "  unfold cW"]
    for i in range(n - 1):
        lines.append(f"  by_cases h{i} : x ≤ {lq(bounds[i+1])}")
        if i < start:
            lines.append(f"  · exfalso; norm_num at hx1 h{i}; linarith")
        else:
            lines.append(f"  · rw [if_pos h{i}]; norm_num")
        lines.append(f"  rw [if_neg h{i}]")
        if i + 1 >= upto:
            lines.append(f"  exfalso; push Not at h{i}; norm_num at hx2; linarith")
            return "\n".join(lines)
    lines.append("  norm_num")
    return "\n".join(lines)
env = "\n\n" + chain_lo("cW_le_315", "{x : ℝ} (hx1 : 1e7 < x) (hx2 : x ≤ 1e8) : cW x ≤ 31.5", 2, 4) + "\n\n" + chain_lo("cW_le_355", "{x : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 3.2e10) : cW x ≤ 35.5", 0, 9) + "\n\n" + chain("cW_le_72", "(x : ℝ) : cW x ≤ 72", 72, n) + "\n\n" + chain("cW_le_33", "{x : ℝ} (hx : x ≤ 1e8) : cW x ≤ 33", 33, 4) + "\n"
txt = txt.replace("\nend TernaryGoldbach.Explicit\n", "\n" + defn + "\n\n" + "\n".join(proof) + "\n" + env + "\nend TernaryGoldbach.Explicit\n")
open('TernaryGoldbach/Explicit/PsiRanges.lean', 'w').write(txt)
