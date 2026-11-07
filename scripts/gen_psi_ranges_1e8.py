# Generates Explicit/PsiRanges1e8.lean: |ψ(x) − x| ≤ c√x on [X, X'] for half-decades in [1e6, 1e17],
# with RH only up to H = 1e8 (rh_upto_1e8, from PlattGRH): Weil windows for |γ| ≤ Y₁ = 4.9e7,
# δ ≥ 7e-8, TailBH ≤ 10.7 e^{−δ²H²/2} (TailBH_1e8_le), Jensen windows on (Y₁, H] with
# e^{−δ²Y₁²/2} LWH(H) ≤ 1142 e^{−δ²Y₁²/2}.
import math, sys
from fractions import Fraction as Q
sys.path.insert(0, 'scripts')
from cert_tables import ELpow, T12, EHpow, T12up
import weil_psi_model as M
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

H8, Y1 = 1e8, 4.9e7
def sep_c8(X0, X1, d, K, y0):
    q = 2*math.exp(-K*K/2)
    u0, u1 = math.sqrt(X0), math.sqrt(X1)
    a = K*d
    tau = 10.7*math.exp(-d*d*H8*H8/2)
    mid = 1142*math.exp(-d*d*Y1*Y1/2)
    LWb = math.exp(d*d/8)*(math.exp(a/2) + math.sqrt(y0/X0))*(M.JW(d) + mid)
    LWbl = math.exp(d*d/8)*(math.exp(-a/2) + math.sqrt(y0/X0))*(M.JW(d) + mid)
    V0 = M.c1*82.6*math.exp(d*d/8)*math.sqrt(2*math.pi)/d/(2*math.pi)
    up = ((math.exp(d*d/2 + a)/(1-q) - 1)*u1 + LWb/(1-q) + tau*u1/(1-q)
          + 4*y0*math.exp(a)/u0 + V0/(1-q)*(math.exp(-a/2)/X0 + 1/math.sqrt(y0*X0)))
    lo = ((1 - math.exp(-a) + 4*math.exp(-K*K/2))*u1 + 2*y0/u0 + LWbl + tau*u1
          + V0*(math.exp(a/2)/X0 + 1/math.sqrt(y0*X0)))
    return max(up, lo)
def expneg_cert(y):
    """(a, f, u) with a + f ≤ y (capped at 60) and e^{−(a+f)} ≤ u."""
    yc = Q(math.floor(min(float(y), 60)*10**6), 10**6)
    assert yc <= y
    a = math.floor(yc); f = yc - a
    u = up_dec(1/(ELpow(a)*T12(f)), 6)
    assert 1 <= u*ELpow(a)*T12(f)
    return a, f, u


NEWCALLS = '''  have hKe : Real.exp ({K} * (1 / {D} : ℝ)) ≤ {E1} :=
    (Real.exp_le_exp.2 (show {K} * (1 / {D} : ℝ) ≤ {F1} by norm_num)).trans hE1
  have hup := psi_range_upH (δ := 1 / {D}) (K := {K}) (y0 := {Y}) (X := {X0}) (X' := {X1}) (c := {C})
    (LU := {LU}) (E1 := {E1}) (E8 := {E8}) (Eh := {Eh}) (q := {Qv}) (sY := {SY}) (sYX := {SYX})
    (rX := {RX}) (rX' := {RX1}) (H := 1e8) (Y₁ := 4.9e7) (τ := {TAU}) (μ := {MU})
    (hRH := rh_upto_1e8) (hH1 := by norm_num) (hH2 := by norm_num) (hY₁0 := by norm_num) (hY₁ := by norm_num)
    (hδ0 := by norm_num) (hδ1 := by norm_num) (hτ := hτ) (hτ0 := by norm_num) (hμ := hμ) (hK := by norm_num) (hKδ := by norm_num) (hy0 := by norm_num)
    (hX1 := by norm_num) (hYX := by nlinarith) (hLU := hLU) (hE1 := by convert hE1 using 2; norm_num)
    (hE8 := by convert hE8 using 2; norm_num) (hEh := by convert hEh using 2; norm_num)
    (hq := by have h := hq; norm_num at h ⊢; linarith) (hq1 := by norm_num) (hsY := hsY) (hsYX := hsYX)
    (hrX0 := by norm_num) (hrX := hrX) (hrX' := hrX') (hc := by norm_num) hx1 hx2
  have hlo := psi_range_loH (δ := 1 / {D}) (K := {K}) (y0 := {Y}) (X := {X0}) (X' := {X1}) (c := {C})
    (LU := {LU}) (E8 := {E8}) (Eh := {Eh}) (q := {Qv}) (sY := {SY}) (sYX := {SYX})
    (rX := {RX}) (rX' := {RX1}) (H := 1e8) (Y₁ := 4.9e7) (τ := {TAU}) (μ := {MU})
    (hRH := rh_upto_1e8) (hH1 := by norm_num) (hH2 := by norm_num) (hY₁0 := by norm_num) (hY₁ := by norm_num)
    (hδ0 := by norm_num) (hδ1 := by norm_num) (hτ := hτ) (hτ0 := by norm_num) (hμ := hμ) (hKδ0 := by norm_num) (hKδ := by norm_num) (hy0 := by norm_num)
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
cexact = []
for i in range(len(bounds) - 1):
    X0, X1 = bounds[i], bounds[i+1]
    # parameters from the model
    best = None
    for kk in range(17, 77):
        d = 10**(-kk/8)
        if not (7e-8 <= d <= 1/208): continue
        for K in [3.5 + 0.1*j for j in range(40)]:
            for jj in range(0, 60):
                y0 = 10**(jj/4)
                if y0*math.exp(K*d) > float(X0): break
                c = sep_c8(float(X0), float(X1), d, K, y0)
                if best is None or c < best[0]: best = (c, d, K, y0)
    c_m, d, K, y0 = best
    D = min(round(1/d), 14285714); delta = Q(1, D); Kq = Q(round(K*10), 10); y0q = Q(round(y0))
    a, f = logup(Q(D)); LU = a + f
    E1 = expup(delta**2/2 + Kq*delta); E8 = expup(delta**2/8); Eh = expup(Kq*delta/2)
    qa, qf, qu = expneg_up(Kq**2/2); q = 2*qu
    sY = sqrt_up(y0q/X0); sYX = up_dec(1/sqrt_lo(y0q*X0), 7)
    rX = sqrt_lo(X0); rX1 = sqrt_up(X1)
    ta, tf, tu = expneg_cert(Q(10**16, 2*D*D)); TAU = up_dec(Q(107, 10)*tu, 6)
    ma, mf, mu = expneg_cert(Q(2401*10**12, 2*D*D)); MU = up_dec(1142*mu, 6)
    JWu = Q(16385, 100000)*LU**2 - Q(4271, 10000)*LU + Q(72032, 10000) + Q(5773, 100)*delta + MU
    Lb = E8*(Eh + sY)*JWu
    cu = (E1/(1-q) - 1)*rX1 + Lb/(1-q) + TAU*rX1/(1-q) + 4*y0q*E1/rX + Q(2533, 10)*E8/delta/(1-q)*(1/X0 + sYX)
    cl = (Kq*delta + 2*q)*rX1 + 2*y0q/rX + Lb + TAU*rX1 + Q(2533, 10)*E8/delta*(Eh/X0 + sYX)
    c = up_dec(max(cu, cl), 4)
    cexact.append(c)
    assert y0q*E1 <= X0
    summary.append((float(X0), float(X1), float(c), D, float(Kq), int(y0q)))
    name = f"psi_range8_{i}"
    calls = NEWCALLS.format(K=lean_q(Kq), D=D, Y=lean_q(y0q), X0=lean_q(X0), X1=lean_q(X1), C=lean_q(c), LU=lean_q(LU), F1=lean_q(delta**2/2 + Kq*delta),
        E1=lean_q(E1), E8=lean_q(E8), Eh=lean_q(Eh), Qv=lean_q(q), SY=lean_q(sY), SYX=lean_q(sYX), RX=lean_q(rX), RX1=lean_q(rX1), TAU=lean_q(TAU), MU=lean_q(MU))
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
  have hg : Real.exp (-((1 / {D} : ℝ) ^ 2 * (1e8 : ℝ) ^ 2 / 2)) ≤ {lean_q(tu)} := by
    have h := exp_neg_le_cert {ta} ({tf.numerator} / {tf.denominator}) ({tu.numerator} / {tu.denominator}) (by norm_num) (by decide +kernel)
    push_cast at h
    exact le_trans (Real.exp_le_exp.2 (by norm_num)) h
  have hτ : ∀ a : ℝ, |a| ≤ 1 → TailBH a (1 / {D}) 1e8 ≤ {lean_q(TAU)} := fun a ha =>
    (TailBH_1e8_le ha (by norm_num) (by norm_num)).trans (by nlinarith)
  have hm : Real.exp (-((1 / {D} : ℝ) ^ 2 * (4.9e7 : ℝ) ^ 2 / 2)) ≤ {lean_q(mu)} := by
    have h := exp_neg_le_cert {ma} ({mf.numerator} / {mf.denominator}) ({mu.numerator} / {mu.denominator}) (by norm_num) (by decide +kernel)
    push_cast at h
    exact le_trans (Real.exp_le_exp.2 (by norm_num)) h
  have hμ : Real.exp (-((1 / {D} : ℝ) ^ 2 * (4.9e7 : ℝ) ^ 2 / 2)) * LWH 1e8 ≤ {lean_q(MU)} := by
    have h1 := LWH_le (H := 1e8) (by norm_num)
    have h0 := LWH_nonneg 1e8
    have h2 := mul_le_mul hm h1 h0 (by norm_num)
    linarith
{calls}  rw [abs_le]; constructor <;> linarith
""")
hdr = '''import TernaryGoldbach.Explicit.PsiRangeCert

variable [Fact TernaryGoldbach.PlattGRH]

/-!
# `|ψ(x) − x| ≤ c √x` on half-decades of `[10⁶, 10¹⁷]` with RH up to `10⁸`

Generated by `scripts/gen_psi_ranges_1e8.py`: from `rh_upto_1e8` (`PlattGRH`
at `q = 1`) through `psi_range_upH` / `psi_range_loH` at `H = 10⁸`, `Y₁ = 4.9·10⁷`, `δ ≥ 7·10⁻⁸`.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology
open TernaryGoldbach.Prelim.Small (T12 ELpow EHpow T12up exp_le_T12up)

namespace TernaryGoldbach.Explicit

'''
with open('TernaryGoldbach/Explicit/PsiRanges1e8.lean', 'w') as fh:
    fh.write(hdr + "".join(out) + "\nend TernaryGoldbach.Explicit\n")
for row in summary: print(row)

# combined statement
def lq(q): return lean_q(q)
cs = [Q(row[2]).limit_denominator(100) for row in summary]
# recompute exact c values as emitted
import re
txt = open('TernaryGoldbach/Explicit/PsiRanges1e8.lean').read()
cvals = re.findall(r"\|psiR x - x\| ≤ \((\d+) / (\d+) : ℝ\) \* √x", txt)
cvals = cexact
n = len(bounds) - 1
defn = "noncomputable def cW8 (x : ℝ) : ℝ :=\n  " + "".join(
    f"if x ≤ {lq(bounds[i+1])} then {lq(cvals[i])} else " for i in range(n - 1)) + lq(cvals[n-1])
proof = ["theorem psi_mid8 {x : ℝ} (h1 : 1e6 ≤ x) (h2 : x ≤ 1e17) : |psiR x - x| ≤ cW8 x * √x := by",
         "  unfold cW8"]
for i in range(n - 1):
    proof.append(f"  by_cases h{i} : x ≤ {lq(bounds[i+1])}")
    lo = "(by norm_num at h1 ⊢; linarith)" if i == 0 else f"(by push Not at h{i-1}; linarith)"
    proof.append(f"  · rw [if_pos h{i}]; exact psi_range8_{i} {lo} h{i}")
    proof.append(f"  rw [if_neg h{i}]")
proof.append(f"  push Not at h{n-2}")
proof.append(f"  exact psi_range8_{n-1} h{n-2}.le (by norm_num at h2 ⊢; linarith)")
def chain(name, stmt, bound, upto):
    lines = ["omit [Fact TernaryGoldbach.PlattGRH] in", f"theorem {name} {stmt} := by", "  unfold cW8"]
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
    """cW8 x ≤ bound for bounds[start] < x ≤ bounds[upto]."""
    lines = ["omit [Fact TernaryGoldbach.PlattGRH] in", f"theorem {name} {stmt} := by", "  unfold cW8"]
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
env = "\n\n" + chain_lo("cW8_le_4282", "{x : ℝ} (hx1 : 3.2e11 < x) (hx2 : x ≤ 3.2e12) : cW8 x ≤ 42.82", 11, 13) + "\n\n" + chain_lo("cW8_le_4508", "{x : ℝ} (hx1 : 3.2e11 < x) (hx2 : x ≤ 1e13) : cW8 x ≤ 45.08", 11, 14) + "\n\n" + chain_lo("cW8_le_315", "{x : ℝ} (hx1 : 1e7 < x) (hx2 : x ≤ 1e8) : cW8 x ≤ 31.5", 2, 4) + "\n\n" + chain_lo("cW8_le_355", "{x : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 3.2e10) : cW8 x ≤ 35.5", 0, 9) + "\n\n" + chain("cW8_le_200", "(x : ℝ) : cW8 x ≤ 200", 200, n) + "\n\n" + chain("cW8_le_72", "{x : ℝ} (hx : x ≤ 1e15) : cW8 x ≤ 72", 72, 18) + "\n\n" + chain("cW8_le_33", "{x : ℝ} (hx : x ≤ 1e8) : cW8 x ≤ 33", 33, 4) + "\n"
txt = txt.replace("\nend TernaryGoldbach.Explicit\n", "\n" + defn + "\n\n" + "\n".join(proof) + "\n" + env + "\nend TernaryGoldbach.Explicit\n")
open('TernaryGoldbach/Explicit/PsiRanges1e8.lean', 'w').write(txt)
