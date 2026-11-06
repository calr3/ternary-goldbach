"""Generate TernaryGoldbach/MinorArcs/NumericsCells.lean: the cell part of `numerics_M`.

Every inequality handed to `norm_num` is first checked here in exact rational arithmetic.
Cells in y = x/49: [Y_k, Y_{k+1}]; block points p_i (ratio rho); certified bounds for
ghat(Y_k, p_i) via `ghatY_le_num`; then `cell_conditions` and `cell_bound`.
"""
from fractions import Fraction as Fr
import math, sys

EM = Fr('2.7182818283'); EP = Fr('2.7182818286')
def taylor6(f): return sum(f**k / math.factorial(k) for k in range(7))
def flog(z): return math.log(z.numerator) - math.log(z.denominator) if isinstance(z, Fr) else math.log(z)
DEC = 10**6
def log_ub(z):
    """(n, f) with z <= EM^n taylor6(f): log z <= n + f."""
    z = Fr(z); v = flog(z); n = int(math.floor(v)); f = Fr(math.ceil((v - n) * DEC) + 1, DEC)
    while not (z <= EM**n * taylor6(f)): f += Fr(1, DEC)
    assert 0 <= f
    return n, f
def log_lb(z):
    """(n, f) with EP^n (taylor6(f) + f^7/4410) <= z, 0 <= f <= 1: n + f <= log z."""
    z = Fr(z); v = flog(z); n = int(math.floor(v)); f = Fr(math.floor((v - n) * DEC) - 1, DEC)
    if f < 0: n -= 1; f += 1
    while not (EP**n * (taylor6(f) + f**7 / 4410) <= z): f -= Fr(1, DEC)
    assert 0 <= f <= 1
    return n, f
def up(x, d=6):
    """a decimal >= x with d significant digits"""
    x = Fr(x); assert x > 0
    e = math.floor(math.log10(x.numerator) - math.log10(x.denominator)) - d + 1
    q = Fr(10)**e
    return math.ceil(x / q) * q
def dn(x, d=6):
    x = Fr(x); assert x > 0
    e = math.floor(math.log10(x.numerator) - math.log10(x.denominator)) - d + 1
    q = Fr(10)**e
    return math.floor(x / q) * q
def lit(x):
    """Lean literal for a Fraction with power-of-10 denominator (or integer)."""
    x = Fr(x)
    if x.denominator == 1: return str(x.numerator)
    k = 0
    while (x * 10**k).denominator != 1:
        k += 1
        assert k < 60, x
    num = abs((x * 10**k).numerator)
    s = str(num).rjust(k + 1, '0')
    r = s[:-k] + '.' + s[-k:]
    return ('-' if x < 0 else '') + r
def nf(n, f): return f"{n} {lit(f)}"
def sqrt_up(a):  # s >= 0 with s^2 >= a
    s = up(Fr(math.sqrt(float(a))) * Fr(1000001, 1000000), 7)
    while s * s < a: s = up(s * Fr(1000001, 1000000), 7)
    return s
def sqrt_dn(a):
    s = dn(Fr(math.sqrt(float(a))) * Fr(999999, 1000000), 7)
    while s * s > a: s = dn(s * Fr(999999, 1000000), 7)
    return s
def cbrt_dn(Y):
    u = dn(Fr(float(Y) ** (1 / 3)) * Fr(999999, 1000000), 7)
    while u**3 > Y: u = dn(u * Fr(999999, 1000000), 7)
    return u

LEAN_LOG_UB = "(log_le_num (z := {z}) {nf} (by norm_num) (by norm_num) (by unfold taylor6; norm_num))"
LEAN_LOG_LB = "(le_log_num (z := {z}) {nf} (by norm_num) (by norm_num) (by unfold taylor6; norm_num))"

def hfun_bound(Y):
    nY, fY = log_ub(Y); ell = nY + fY
    sq = sqrt_up(ell)
    t = up(Fr(float(Y) ** (-1 / 6)) * Fr(1000001, 1000000), 7)
    while (1 / t) ** 6 > Y: t = up(t * Fr(1000001, 1000000), 7)
    h = up(Fr('0.276') * t * (ell * sq) + 1234 * t * t * ell, 7)
    return dict(nY=nY, fY=fY, ell=ell, sq=sq, t=t, h=h)

def ghat_eval(name, Y, Ylit, M, H):
    """Lean lemma `name : ghatY Y M ≤ G`; returns (lean, G)."""
    Mf = Fr(M)
    u = cbrt_dn(Y); assert u**3 <= Y and Mf <= u / 6
    n1, f1 = log_ub(2 * Mf); a1 = n1 + f1
    n2, f2 = log_ub(8 * Mf); b1 = n2 + f2
    z3 = 9 * u / (Fr('4.008') * Mf); n3, f3 = log_lb(z3); b2 = n3 + f3; assert b2 > 0
    z4 = 1 + b1 / (2 * b2); n4, f4 = log_ub(z4); rho = n4 + f4
    n5, f5 = log_ub(Mf); m1 = n5 + f5; n6, f6 = log_ub(m1); c1 = n6 + f6
    n7, f7 = log_lb(Mf); m2 = n7 + f7; n8, f8 = log_lb(m2); c2 = n8 + f8; assert c2 > 0
    phi1 = Fr('1.7882') * c1 + Fr('2.50637') / c2
    s1 = sqrt_up(phi1); s2 = sqrt_dn(2 * Mf)
    t1 = H['t']; h1 = H['h']
    E1 = 1398 * ((((Fr('0.27125') * rho + Fr('0.41415')) * a1 + Fr('0.8764')) * s1 + Fr('2.526')) / s2 +
                 (phi1 * (Fr(13, 4) * a1 + Fr('7.82')) + Fr('13.66') * a1 + Fr('37.55')) / Mf + Fr('3.8') * t1) / 1000 \
         + 17 * (670 / Mf) ** 3 / 3
    E2 = Fr('1.398') * h1 + 17 * (670 / Mf) ** 3 / 3
    G = up(max(E1, E2), 6)
    Ml = f"(({M} : ℕ) : ℝ)"
    L = []
    L.append(f"theorem {name} : ghatY ({Ylit} : ℝ) {Ml} ≤ {lit(G)} := by")
    L.append(f"  refine ghatY_le_num (u := {lit(u)}) (a₁ := {lit(a1)}) (b₁ := {lit(b1)}) (b₂ := {lit(b2)})")
    L.append(f"    (ρ := {lit(rho)}) (c₁ := {lit(c1)}) (c₂ := {lit(c2)}) (s₁ := {lit(s1)}) (s₂ := {lit(s2)})")
    L.append(f"    (t₁ := {lit(t1)}) (h₁ := {lit(h1)}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
    L.append(f"    (by norm_num) ?_ ?_ ?_ (by norm_num) ?_ ?_ ?_ (by norm_num) (by norm_num) (by norm_num)")
    L.append(f"    (by norm_num) (by norm_num) ?_ ?_ (by norm_num) (by norm_num)")
    L.append(f"  · exact {LEAN_LOG_UB.format(z=f'2 * {Ml}', nf=nf(n1,f1))}.trans (by norm_num)")
    L.append(f"  · exact {LEAN_LOG_UB.format(z=f'8 * {Ml}', nf=nf(n2,f2))}.trans (by norm_num)")
    L.append(f"  · exact (by norm_num : ({lit(b2)} : ℝ) ≤ ({n3} : ℕ) + {lit(f3)}).trans")
    L.append(f"      {LEAN_LOG_LB.format(z=f'9 * {lit(u)} / (4.008 * {Ml})', nf=nf(n3,f3))}")
    L.append(f"  · exact {LEAN_LOG_UB.format(z=f'1 + {lit(b1)} / (2 * {lit(b2)})', nf=nf(n4,f4))}.trans (by norm_num)")
    L.append(f"  · refine (Real.log_le_log (Real.log_pos (by norm_num))")
    L.append(f"      ({LEAN_LOG_UB.format(z=Ml, nf=nf(n5,f5))}.trans (by norm_num : (({n5} : ℕ) : ℝ) + {lit(f5)} ≤ {lit(m1)}))).trans ?_")
    L.append(f"    exact {LEAN_LOG_UB.format(z=lit(m1), nf=nf(n6,f6))}.trans (by norm_num)")
    L.append(f"  · refine (by norm_num : ({lit(c2)} : ℝ) ≤ ({n8} : ℕ) + {lit(f8)}).trans")
    L.append(f"      ({LEAN_LOG_LB.format(z=lit(m2), nf=nf(n8,f8))}.trans (Real.log_le_log (by norm_num) ?_))")
    L.append(f"    exact (by norm_num : ({lit(m2)} : ℝ) ≤ ({n7} : ℕ) + {lit(f7)}).trans {LEAN_LOG_LB.format(z=Ml, nf=nf(n7,f7))}")
    L.append(f"  · exact rpow_neg_sixth_le (by norm_num) (by norm_num)")
    L.append(f"  · exact (hfun_le_num (sq := {lit(H['sq'])}) (by norm_num) ({LEAN_LOG_UB.format(z=Ylit, nf=nf(H['nY'],H['fY']))}.trans")
    L.append(f"      (by norm_num : (({H['nY']} : ℕ) : ℝ) + {lit(H['fY'])} ≤ {lit(H['ell'])})) (by norm_num) (by norm_num)")
    L.append(f"      (rpow_neg_sixth_le (t := {lit(t1)}) (by norm_num) (by norm_num))).trans (by norm_num)")
    return "\n".join(L), G


# ---------------------------------------------------------------------------------------------
def r2max(X):
    Q = math.sqrt(float(X) / 784)
    return int(min((2 * Q) ** 0.6 / 2, Q / 20000)) - 2

def cell(k, Y, Ylit, Y2, Y2lit, rho):
    X = 49 * Y; X2 = 49 * Y2
    r2 = r2max(X)
    # exact checks of the size conditions at X
    assert (20000 * r2) ** 2 <= X / 784 and (2 * r2) ** 10 <= (4 * X / 784) ** 3
    assert (6 * r2) ** 3 <= X / 49 and Fr('2.16e20') * r2 <= 670 * (X / 49)
    pts = [150001]
    while pts[-1] < r2:
        pts.append(min(int(pts[-1] * rho) + 1, r2))
    kk = len(pts) - 1
    assert (6 * r2) ** 3 <= Y
    H = hfun_bound(Y)
    out = []; Gs = []
    s, G0 = ghat_eval(f"c{k}_g0", Y, Ylit, 150000, H); out.append(s)
    for i in range(kk):
        s, G = ghat_eval(f"c{k}_p{i}", Y, Ylit, pts[i], H); out.append(s); Gs.append(G)
    s, Gt = ghat_eval(f"c{k}_gt", Y, Ylit, r2, H); out.append(s)
    # logs of block ratios
    ells = []; lproofs = []
    for i in range(kk):
        z = Fr(pts[i + 1], pts[i]); n, f = log_ub(z); ells.append(n + f); lproofs.append((n, f))
    # L0 <= log X, log X2 <= L1
    nA, fA = log_lb(X); L0 = nA + fA
    nB, fB = log_ub(X2); L1 = nB + fB
    # cL bounds
    nC, fC = log_ub(Fr(2 * 150001)); cl0 = nC + fC + Fr('2')
    nD, fD = log_lb(Fr(2 * r2)); clt = nD + fD + Fr('2')
    nE, fE = log_ub(Fr(2 * r2)); lr = nE + fE
    assert lr + Fr('2') <= L0 / 2 - Fr('1.3066')
    a = Fr('0.640208000017'); b = Fr('0.021095')
    sD = up((a * L0 - b) / (L0 / 2 - Fr('1.3066')), 7)
    tau = up((a * L1 - b) * (1 - clt / (L1 / 2 - Fr('1.3064'))), 7)
    assert Fr('8.6294') <= cl0 * sD and tau >= 0
    total = G0 * (cl0 * sD - Fr('8.6294')) + sD * sum(Gs[i] * ells[i] for i in range(kk)) + Gt * tau
    assert total <= Fr('1.037'), (k, float(total))
    print(f"-- cell {k}: total {float(total):.5f}", file=sys.stderr)
    plist = "[" + ", ".join(str(p) for p in pts) + "]"
    glist = "[" + ", ".join(lit(g) for g in Gs) + "]"
    llist = "[" + ", ".join(lit(l) for l in ells) + "]"
    L = []
    L.append(f"theorem cell{k} {{x : ℝ}} (hx1 : ({lit(X)} : ℝ) ≤ x) (hx2 : x ≤ ({lit(X2)} : ℝ)) :")
    L.append("    ∃ r₂ : ℕ, 150000 < r₂ ∧ (20000 * (r₂ : ℝ)) ^ 2 ≤ x / 784 ∧")
    L.append("      2 * (r₂ : ℝ) ≤ (2 * √(x / 784)) ^ (0.6 : ℝ) ∧ (r₂ : ℝ) ≤ (x / κ) ^ (1 / 3 : ℝ) / 6 ∧")
    L.append("      2.16e20 * r₂ ≤ 670 * (x / κ) ∧ cL (r₂ - 1) ≤ Dx x ∧ Mexpr x r₂ ≤ 1.037 := by")
    L.append(f"  have hx : 4.9e26 ≤ x := le_trans (by norm_num) hx1")
    L.append(f"  have hL₀x : ({lit(L0)} : ℝ) ≤ Real.log x := (by norm_num : ({lit(L0)} : ℝ) ≤ ({nA} : ℕ) + {lit(fA)}).trans")
    L.append(f"    ({LEAN_LOG_LB.format(z=lit(X), nf=nf(nA,fA))}.trans (Real.log_le_log (by norm_num) hx1))")
    L.append(f"  have hL₁x : Real.log x ≤ ({lit(L1)} : ℝ) := (Real.log_le_log (by linarith) hx2).trans")
    L.append(f"    ({LEAN_LOG_UB.format(z=lit(X2), nf=nf(nB,fB))}.trans (by norm_num))")
    L.append(f"  obtain ⟨c1, c2, c3, c4, c5⟩ := cell_conditions (X := {lit(X)}) (ℓr := {lit(lr)}) (L₀ := {lit(L0)})")
    L.append(f"    (r₂ := {r2}) hx1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
    L.append(f"    ({LEAN_LOG_UB.format(z=f'2 * (({r2} : ℕ) : ℝ)', nf=nf(nE,fE))}.trans (by norm_num)) (by norm_num) hL₀x")
    L.append(f"  refine ⟨{r2}, by norm_num, c1, c2, c3, c4, c5, ?_⟩")
    L.append(f"  refine cell_bound (Y := {Ylit}) (L₀ := {lit(L0)}) (L₁ := {lit(L1)}) (cl0 := {lit(cl0)}) (clt := {lit(clt)})")
    L.append(f"    (G0 := {lit(G0)}) (Gt := {lit(Gt)}) (sD' := {lit(sD)}) (τ' := {lit(tau)}) (k := {kk})")
    L.append(f"    (fun i => {plist}.getD i 0) (fun i => ({glist} : List ℝ).getD i 0)")
    L.append(f"    (fun i => ({llist} : List ℝ).getD i 0) hx (by norm_num)")
    L.append(f"    (by rw [show (κ : ℝ) = 49 from rfl, le_div_iff₀ (by norm_num)]; linarith) (by norm_num) hL₀x hL₁x")
    L.append(f"    rfl rfl (by intro i hi; interval_cases i <;> decide)")
    L.append(f"    ((by norm_num : (({r2} : ℕ) : ℝ) ≤ {lit(cbrt_dn(Y))} / 6).trans (by")
    L.append(f"      have := le_rpow_third (Y := ({Ylit} : ℝ)) (u := {lit(cbrt_dn(Y))}) (by norm_num) (by norm_num); linarith))")
    L.append(f"    (by intro i hi; interval_cases i")
    for i in range(kk):
        L.append(f"        · exact c{k}_p{i}")
    L.append(f"      )")
    L.append(f"    (by intro i hi; interval_cases i")
    for i in range(kk):
        n, f = lproofs[i]
        L.append(f"        · show Real.log ((({pts[i+1]} : ℕ) : ℝ) / (({pts[i]} : ℕ) : ℝ)) ≤ {lit(ells[i])}")
        L.append(f"          exact {LEAN_LOG_UB.format(z=f'(({pts[i+1]} : ℕ) : ℝ) / (({pts[i]} : ℕ) : ℝ)', nf=nf(n,f))}.trans (by norm_num)")
    L.append(f"      )")
    L.append(f"    c{k}_g0 c{k}_gt")
    L.append(f"    (cL_le (by have h := {LEAN_LOG_UB.format(z=f'2 * (((150000 : ℕ) : ℝ) + 1)', nf=nf(nC,fC))};"
             f" norm_num at h ⊢; linarith))")
    L.append(f"    (le_cL_pred (by norm_num) (by have h := {LEAN_LOG_LB.format(z=f'2 * (({r2} : ℕ) : ℝ)', nf=nf(nD,fD))};"
             f" norm_num at h ⊢; linarith))")
    L.append(f"    (by norm_num) c5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
    L.append(f"    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ,")
    L.append(f"      List.getD_cons_zero]; norm_num)")
    if k == len(CELLS) - 1:
        S = sum(Gs[i] * ells[i] for i in range(kk))
        C = []
        C.append(f"/-- The block chain of cell {k}, for every `y ≥ Y_{k}` (used for `y ≥ 10¹⁰⁰`). -/")
        C.append(f"theorem chain{k} {{y : ℝ}} (hy : ({Ylit} : ℝ) ≤ y) :")
        C.append(f"    ∑ n ∈ Finset.Ico (150001 : ℕ) {r2}, ghatY y n * Real.log (((n : ℝ) + 1) / n) ≤ {lit(S)} := by")
        C.append(f"  have h := chain_le (Y := {Ylit}) (k := {kk}) (fun i => {plist}.getD i 0)")
        C.append(f"    (fun i => ({glist} : List ℝ).getD i 0) (fun i => ({llist} : List ℝ).getD i 0)")
        C.append(f"    (by norm_num) hy (by decide) (by intro i hi; interval_cases i <;> decide)")
        C.append(f"    ((by norm_num : (({r2} : ℕ) : ℝ) ≤ {lit(cbrt_dn(Y))} / 6).trans (by")
        C.append(f"      have := le_rpow_third (Y := ({Ylit} : ℝ)) (u := {lit(cbrt_dn(Y))}) (by norm_num) (by norm_num); linarith))")
        C.append(f"    (by intro i hi; interval_cases i")
        for i in range(kk):
            C.append(f"        · exact c{k}_p{i}")
        C.append(f"      )")
        C.append(f"    (by intro i hi; interval_cases i")
        for i in range(kk):
            n, f = lproofs[i]
            C.append(f"        · show Real.log ((({pts[i+1]} : ℕ) : ℝ) / (({pts[i]} : ℕ) : ℝ)) ≤ {lit(ells[i])}")
            C.append(f"          exact {LEAN_LOG_UB.format(z=f'(({pts[i+1]} : ℕ) : ℝ) / (({pts[i]} : ℕ) : ℝ)', nf=nf(n,f))}.trans (by norm_num)")
        C.append(f"      )")
        C.append(f"  refine le_trans h (le_of_eq ?_)")
        C.append(f"  simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_succ, List.getD_cons_zero]")
        C.append(f"  norm_num")
        print(f"-- chain{k}: S = {float(S):.6f}, r2 = {r2}, G0 = {float(G0):.6f}", file=sys.stderr)
        return out + ["\n".join(L), "\n".join(C)]
    return out + ["\n".join(L)]

CELLS = [(Fr(10)**25, "1e25", Fr(3)*Fr(10)**25, "3e25", 1.4),
         (Fr(3)*Fr(10)**25, "3e25", Fr(10)**26, "1e26", 1.6),
         (Fr(10)**26, "1e26", Fr(10)**27, "1e27", 1.6),
         (Fr(10)**27, "1e27", Fr(10)**28, "1e28", 2),
         (Fr(10)**28, "1e28", Fr(10)**30, "1e30", 2),
         (Fr(10)**30, "1e30", Fr(10)**34, "1e34", 2.5),
         (Fr(10)**34, "1e34", Fr(10)**42, "1e42", 3),
         (Fr(10)**42, "1e42", Fr(10)**58, "1e58", 4),
         (Fr(10)**58, "1e58", Fr(10)**100, "1e100", 6)]

def main(which=None):
    hdr = ["import TernaryGoldbach.MinorArcs.NumericsCore", "",
           "variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.PlattGRH]",
           "  [Fact TernaryGoldbach.ButhePsi] [Fact TernaryGoldbach.RamareMoebius]", "",
           "/-! Generated by `scripts/gen_cells.py`: the cells `y ∈ [Y_k, Y_{k+1}]` of `numerics_M`. -/", "",
           "open Real", "open TernaryGoldbach.Helfgott (κ)", "", "namespace TernaryGoldbach.MinorArcs", ""]
    body = []
    for k, (Y, Yl, Y2, Y2l, rho) in enumerate(CELLS):
        if which is not None and k not in which: continue
        body += cell(k, Y, Yl, Y2, Y2l, rho)
    return "\n".join(hdr + ["\n\n".join(body), "", "end TernaryGoldbach.MinorArcs", ""])

if __name__ == "__main__":
    open("TernaryGoldbach/MinorArcs/NumericsCells.lean", "w").write(main())
