import TernaryGoldbach.Explicit.ZetaZeroSums
import TernaryGoldbach.Explicit.PsiSandwich
import TernaryGoldbach.Explicit.ExplicitBoundGen

/-!
# The explicit-formula bound for the Gaussian-smoothed prime sum

`|Σ Λ(n) φ(n/x) − M(1) x| ≤ √x·LineB2 + x·TailB + x^{−1/2} V/(2π)` for `φ = gsm a b δ`, unconditionally
(RH to `3·10¹²` is the numerical axiom `rh_upto`).
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

theorem norm_logDeriv_zeta_left (y : ℝ) :
    ‖logDeriv riemannZeta (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ (2 / Real.log 2 + 4.8) * (3 + 37 + 2.6 * |y|) := by
  set c₁ := 2 / Real.log 2 + 4.8 with hc₁
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hc₁0 : 0 ≤ c₁ := by positivity
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
  have hsre : s.re = -1 / 2 := by simp [hs]
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsre; simp at hsre; norm_num at hsre
  have hz : riemannZeta s ≠ 0 :=
    zeta_ne_zero_of_zetaF hs1 (zetaF_ne_zero_strip (by rw [hsre]; norm_num) (by rw [hsre]; norm_num))
  have hld : logDeriv riemannZeta s = logDeriv zetaF s - 1 / (s - 1) := by
    rw [logDeriv_zetaF_eq hs1 hz]; ring
  have hL := norm_logDeriv_leftD ldatum_zeta y
  have hLB := log_Bz_le y
  have hL' : ‖logDeriv zetaF s‖ ≤ c₁ * (39 + 2.6 * |y|) := by
    refine hL.trans ?_
    have e : Real.log (Bz y / 0.355) / Real.log 2 / (1 / 2) + 4.8 * Real.log (Bz y / 0.355) =
        c₁ * Real.log (Bz y / 0.355) := by rw [hc₁]; ring
    rw [e]; exact mul_le_mul_of_nonneg_left (by linarith) hc₁0
  have hinv : ‖1 / (s - 1)‖ ≤ 2 / 3 := by
    rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hs1))]
    have := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, hsre] at this
    norm_num at this ⊢; linarith
  have hc₁1 : 2 / 3 ≤ c₁ := by
    have : 0 ≤ 2 / Real.log 2 := by positivity
    rw [hc₁]; linarith
  rw [hld]; refine (norm_sub_le _ _).trans ?_; nlinarith

/-- `V = c₁ · 82.6 · e^{δ²/8} (e^{−a/2} + e^{−b/2}) √(2π)/δ`. -/
noncomputable def Vg (a b δ : ℝ) : ℝ :=
  (2 / Real.log 2 + 4.8) * 82.6 * Real.exp (δ ^ 2 / 8) * (Real.exp (-(a / 2)) + Real.exp (-(b / 2))) *
    (√(2 * π) / δ)

theorem norm_integral_hZeta_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) {x : ℝ} (hx : 0 < x) :
    ‖∫ y : ℝ, hZeta (fun u => (gsm a b δ u : ℂ)) x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      x ^ (-(1 / 2) : ℝ) * Vg a b δ := by
  set c₁ := 2 / Real.log 2 + 4.8 with hc₁
  have hc₁0 : 0 ≤ c₁ := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  set A := c₁ * 82.6 * Real.exp (δ ^ 2 / 8) * (Real.exp (-(a / 2)) + Real.exp (-(b / 2))) with hA
  have hA0 : 0 ≤ A := by positivity
  set g : ℝ → ℝ := fun y => x ^ (-(1 / 2) : ℝ) * A * Real.exp (-(δ ^ 2 / 2) * y ^ 2) with hg
  have hgi : Integrable g := (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  have hpt : ∀ y : ℝ, ‖hZeta (fun u => (gsm a b δ u : ℂ)) x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ g y := by
    intro y
    set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
    have hsre : s.re = -1 / 2 := by simp [hs]
    have hsim : s.im = y := by simp [hs]
    have hs0 : s ≠ 0 := by intro h; rw [h] at hsre; norm_num at hsre
    rw [hZeta, norm_mul, norm_mul, norm_cpow_x hx, hsre, mellin_gsm hδ hab, Mg, norm_mul, norm_cexp_gauss]
    have hζ := norm_logDeriv_zeta_left y
    have hI := norm_intExp_le' (a := a) (b := b) hs0
    rw [hsre] at hI
    have hsn1 : 1 / 2 ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s; rw [hsre] at this; norm_num at this; linarith
    have hsn2 : |y| ≤ ‖s‖ := by have := Complex.abs_im_le_norm s; rwa [hsim] at this
    have hspos : 0 < ‖s‖ := by linarith
    have hratio : (3 + 37 + 2.6 * |y|) / ‖s‖ ≤ 82.6 := by
      rw [div_le_iff₀ hspos]; nlinarith [abs_nonneg y]
    have hgauss : Real.exp (δ ^ 2 * (s.re ^ 2 - s.im ^ 2) / 2) = Real.exp (δ ^ 2 / 8) * Real.exp (-(δ ^ 2 / 2) * y ^ 2) := by
      rw [hsre, hsim, ← Real.exp_add]; congr 1; ring
    rw [hgauss]
    have e1 : Real.exp (a * (-1 / 2)) = Real.exp (-(a / 2)) := by congr 1; ring
    have e2 : Real.exp (b * (-1 / 2)) = Real.exp (-(b / 2)) := by congr 1; ring
    rw [e1, e2] at hI
    have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
    have e3 : x ^ (-1 / 2 : ℝ) = x ^ (-(1 / 2) : ℝ) := by norm_num
    calc ‖logDeriv riemannZeta s‖ * (Real.exp (δ ^ 2 / 8) * Real.exp (-(δ ^ 2 / 2) * y ^ 2) *
          ‖∫ w in b..a, cexp (s * w)‖ * x ^ (-1 / 2 : ℝ))
        ≤ (c₁ * (3 + 37 + 2.6 * |y|)) * (Real.exp (δ ^ 2 / 8) * Real.exp (-(δ ^ 2 / 2) * y ^ 2) *
          ((Real.exp (-(a / 2)) + Real.exp (-(b / 2))) / ‖s‖) * x ^ (-1 / 2 : ℝ)) := by
          gcongr
      _ = x ^ (-1 / 2 : ℝ) * (c₁ * ((3 + 37 + 2.6 * |y|) / ‖s‖) * Real.exp (δ ^ 2 / 8) *
          (Real.exp (-(a / 2)) + Real.exp (-(b / 2)))) * Real.exp (-(δ ^ 2 / 2) * y ^ 2) := by
          field_simp
      _ ≤ x ^ (-1 / 2 : ℝ) * A * Real.exp (-(δ ^ 2 / 2) * y ^ 2) := by
          rw [hA]; gcongr
      _ = g y := by rw [hg, e3]
  refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [hg, integral_const_mul, integral_gaussian]
  unfold Vg
  rw [← hc₁, ← hA]
  have : √(π / (δ ^ 2 / 2)) = √(2 * π) / δ := by
    rw [show π / (δ ^ 2 / 2) = (2 * π) / δ ^ 2 by field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hδ.le]
  rw [this]; ring

/-- The line-zero constant. -/
noncomputable def LineB (a δ : ℝ) : ℝ :=
  ZLg BPz2 3e12 * (2 * Real.exp (δ ^ 2 / 2 + |a|)) * (4 * (1 + (1 + Real.log (Jl 3e12)) / 3.48))

/-- The sharper line-zero constant (`line_sum_leH` with windows of height `6`, radius `3.36`, the two
next to the real axis counted at height `3`; `norm_Mg_line_le'`), used by `SsumG_gsm_err`. -/
noncomputable def LineB2 (a b δ : ℝ) : ℝ :=
  (Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (b / 2))) *
    (4 * ZL0 6 3.36 + 2 * ZLh 6 3.36 3e12 * (1 + Real.log (JlH 6 3e12)) / 6)

/-- The tail constant (zeros above `3·10¹²`). -/
noncomputable def TailB (a δ : ℝ) : ℝ :=
  EBg a δ 3e12 * (2 * Z3g BPz2 3e12 / (1 - rhoG δ 3e12) + 2 * c3g 10 3e12 / (1 - rhoG δ 3e12) ^ 2)

/-- **The explicit-formula bound for the smoothed sum.** -/
theorem SsumG_gsm_err {a b δ x : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 ≤ x) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fun u => (gsm a b δ u : ℂ)) x - Mg a b δ 1 * x‖ ≤
      √x * LineB2 a b δ + x * TailB a δ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hM : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hgood hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      √x * LineB2 a b δ + x * TailB a δ := by
    intro T
    set Z := zerosRectD zetaF T with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
    have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
        ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0, hM]
    refine h1.trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ 3e12)]
    refine add_le_add ?_ ?_
    · -- the line zeros
      set S := Z.filter (fun u => |u.im| ≤ 3e12) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have hre : ∀ u ∈ S, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
        exact rh_upto u hz hr1 hr2 hu2
      have him : ∀ u ∈ S, |u.im| ≤ 3e12 := fun u hu => (Finset.mem_filter.1 hu).2
      have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
        intro u hu
        rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      refine line_sum_leH (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) S hSZ hre him
        (fun u => ‖Mg a b δ u‖) (fun u _ => norm_nonneg _) (by positivity) (fun u hu => ?_)
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hu']
      have := norm_Mg_line_le' a b δ u.im
      simpa using this
    · -- zeros above `3·10¹²`
      set S := Z.filter (fun u => ¬ |u.im| ≤ 3e12) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have him : ∀ u ∈ S, 3e12 < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
      exact tail_sum_gauss (by norm_num) hδ hb hx S hSZ him
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * LineB2 a b δ + x * TailB a δ :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k => hbound (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤ x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hZeta_gsm hδ hab hx0) (by positivity)
  have e : SsumG (1 : DirichletCharacter ℂ 1) φ x - Mg a b δ 1 * x =
      -((mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0) +
        (1 / (2 * π) : ℂ) * I0) := by rw [hM]; ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-! ## Two-sided bounds for `ψ(x)` -/

/-- The total explicit-formula error. -/
noncomputable def ErrG (a b δ x : ℝ) : ℝ :=
  √x * LineB2 a b δ + x * TailB a δ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π)

theorem summable_gsm {a b δ x : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hx : 0 < x) :
    Summable fun n : ℕ => Λ n * gsm a b δ (n / x) := by
  have h := summable_SsumG (1 : DirichletCharacter ℂ 1) (goodSmoothing_gsm hδ hab) hx
  have h2 := Complex.reCLM.summable h
  refine h2.congr fun n => ?_
  simp only [Complex.reCLM_apply]
  rw [MulChar.one_apply (isUnit_of_subsingleton _)]
  simp

theorem tsum_gsm_le {a b δ x : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (hb : b ≤ 0) (hx : 1 ≤ x) :
    |∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x| ≤ ErrG a b δ x := by
  have h := SsumG_gsm_err hδ hab hb hx
  rw [SsumG_one_ofReal, Mg_one] at h
  rw [show ((∑' n : ℕ, Λ n * gsm a b δ (n / x) : ℝ) : ℂ) -
      ((Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) : ℝ) : ℂ) * (x : ℂ) =
      ((∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **Upper bound for `ψ`.** -/
theorem psi_upper_explicit {δ K y0 x : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hK1 : 2 * Real.exp (-(K ^ 2 / 2)) < 1)
    (hy0 : 0 < y0) (hx : 1 ≤ x) (hYx : y0 * Real.exp (K * δ) ≤ x) :
    psiR x ≤ 4 * (y0 * Real.exp (K * δ)) +
      (Real.exp (δ ^ 2 / 2 + K * δ) * x + ErrG (K * δ) (Real.log (y0 / x)) δ x) /
        (1 - 2 * Real.exp (-(K ^ 2 / 2))) := by
  have hx0 : 0 < x := by linarith
  have hb : Real.log (y0 / x) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one hx0).2
    (le_trans (le_mul_of_one_le_right hy0.le (Real.one_le_exp (by positivity))) hYx))
  have hab : Real.log (y0 / x) ≤ K * δ := hb.trans (by positivity)
  have hS := sandwich_upper hδ hK hy0 hx0 hYx (summable_gsm hδ hab hx0)
  have hT := tsum_gsm_le hδ hab hb hx
  have hc : 0 < 1 - 2 * Real.exp (-(K ^ 2 / 2)) := by linarith
  have hmain : Real.exp (δ ^ 2 / 2) * (Real.exp (K * δ) - Real.exp (Real.log (y0 / x))) * x ≤
      Real.exp (δ ^ 2 / 2 + K * δ) * x := by
    rw [Real.exp_add]
    have hp : 0 < Real.exp (δ ^ 2 / 2) * Real.exp (Real.log (y0 / x)) * x :=
      mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hx0
    have e : Real.exp (δ ^ 2 / 2) * (Real.exp (K * δ) - Real.exp (Real.log (y0 / x))) * x =
        Real.exp (δ ^ 2 / 2) * Real.exp (K * δ) * x - Real.exp (δ ^ 2 / 2) * Real.exp (Real.log (y0 / x)) * x := by
      ring
    rw [e]; linarith
  have hsum : ∑' n : ℕ, Λ n * gsm (K * δ) (Real.log (y0 / x)) δ (n / x) ≤
      Real.exp (δ ^ 2 / 2 + K * δ) * x + ErrG (K * δ) (Real.log (y0 / x)) δ x := by
    have := (abs_le.1 hT).2; linarith
  have hY := psiR_le (y := y0 * Real.exp (K * δ)) (by positivity)
  have h1 : psiR x - psiR (y0 * Real.exp (K * δ)) ≤
      (Real.exp (δ ^ 2 / 2 + K * δ) * x + ErrG (K * δ) (Real.log (y0 / x)) δ x) / (1 - 2 * Real.exp (-(K ^ 2 / 2))) := by
    rw [le_div_iff₀ hc]; nlinarith
  linarith

/-- **Lower bound for `ψ`.** -/
theorem psi_lower_explicit {δ K y0 x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hKδ : δ ≤ K) (hy0 : 0 < y0)
    (hx : 1 ≤ x) (hb : Real.log (y0 / x) ≤ -(K * δ)) :
    Real.exp (-(K * δ)) * x - 2 * y0 - ErrG (-(K * δ)) (Real.log (y0 / x)) δ x -
      4 * x * Real.exp (-(K ^ 2 / 2)) ≤ psiR x := by
  have hx0 : 0 < x := by linarith
  have hb0 : Real.log (y0 / x) ≤ 0 := hb.trans (by have : 0 ≤ K * δ := by nlinarith
                                                   linarith)
  have hS := sandwich_lower hδ hKδ hx0 hb
  have hT := tsum_gsm_le hδ hb hb0 hx
  have he : Real.exp (Real.log (y0 / x)) = y0 / x := Real.exp_log (by positivity)
  rw [he] at hT
  have hd : Real.exp (δ ^ 2 / 2) ≤ 2 := by
    have : Real.exp (δ ^ 2 / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : Real.exp (1 / 2) ≤ 2 := by
      have := Real.exp_one_lt_d9
      have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    linarith
  have hd1 : 1 ≤ Real.exp (δ ^ 2 / 2) := Real.one_le_exp (by positivity)
  have hmain : Real.exp (-(K * δ)) * x - 2 * y0 ≤
      Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) - y0 / x) * x := by
    have e : Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) - y0 / x) * x =
        Real.exp (δ ^ 2 / 2) * Real.exp (-(K * δ)) * x - Real.exp (δ ^ 2 / 2) * y0 := by
      field_simp
    rw [e]
    have hq : 0 ≤ Real.exp (-(K * δ)) * x := (mul_pos (Real.exp_pos _) hx0).le
    have h1 : 1 * (Real.exp (-(K * δ)) * x) ≤ Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) * x) :=
      mul_le_mul_of_nonneg_right hd1 hq
    have h2 : Real.exp (δ ^ 2 / 2) * y0 ≤ 2 * y0 := mul_le_mul_of_nonneg_right hd hy0.le
    have e2 : Real.exp (δ ^ 2 / 2) * (Real.exp (-(K * δ)) * x) = Real.exp (δ ^ 2 / 2) * Real.exp (-(K * δ)) * x := by ring
    rw [e2, one_mul] at h1
    linarith
  have := (abs_le.1 hT).1
  linarith

end TernaryGoldbach.Explicit
