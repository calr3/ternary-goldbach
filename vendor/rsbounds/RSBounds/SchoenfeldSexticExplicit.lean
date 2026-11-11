import RSBounds.PolynomialExplicitFormula
import RSBounds.PolynomialPrimeSum
import RSBounds.PolynomialZetaFormula
import RSBounds.SchoenfeldSexticMellin
import RSBounds.SchoenfeldSexticPsi
import TernaryGoldbach.Explicit.ZetaExplicit
import TernaryGoldbach.Explicit.ExplicitFormula
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The sextic explicit formula with an explicit left remainder

The order-6 analogue of `PolynomialQuarticFormula`, `PolynomialPsiMellin` and
`PolynomialZetaFormula`. The contour machinery of `PolynomialExplicitFormula` is generic in the
kernel; it needs a holomorphic numerator `H` with kernel `H(s)/s` and inverse-fifth-power decay
(`DecayFive`). The sextic kernel `1/(s(s+1)⋯(s+6))` decays like `|t|^{-7}`, so it qualifies.

The result (`explicit_formula_Psi6_at_heights`) is

    Ψ₆(x) = x⁷/5040 − lim ∑_{|γ|<T_k} m_ρ x^{ρ+6}/(ρ(ρ+1)⋯(ρ+6)) − x⁶ log(2π)/720 − E₆(x),

with `Ψ₆(x) = ∑ Λ(n)(x−n)₊⁶/720` and `E₆` the left vertical integral on `Re s = −1/2`, kept
explicit. The zero sums are over the zeros of `(s−1)ζ(s)` in the rectangle, with multiplicity,
along any good-height sequence.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.SchoenfeldSexticExplicit

open TernaryGoldbach.Explicit PolynomialExplicit SchoenfeldSexticMellin SchoenfeldSexticPsi

/-! ## The kernel -/

noncomputable def numerator (s : ℂ) : ℂ :=
  1 / ((s + 1) * (s + 2) * (s + 3) * (s + 4) * (s + 5) * (s + 6))

theorem kernel_eq_numerator_div (s : ℂ) : kernel s = numerator s / s := by
  simp only [kernel, numerator, div_div]
  congr 1
  ring

theorem numerator_zero : numerator 0 = 1 / 720 := by
  norm_num [numerator]

theorem differentiableAt_numerator {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ numerator s := by
  have hn (n : ℕ) (hn : 1 ≤ n) : s + n ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [add_re, natCast_re, zero_re] at he
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : s + 1 ≠ 0 := by simpa using hn 1 le_rfl
  have h2 : s + 2 ≠ 0 := by simpa using hn 2 (by omega)
  have h3 : s + 3 ≠ 0 := by simpa using hn 3 (by omega)
  have h4 : s + 4 ≠ 0 := by simpa using hn 4 (by omega)
  have h5 : s + 5 ≠ 0 := by simpa using hn 5 (by omega)
  have h6 : s + 6 ≠ 0 := by simpa using hn 6 (by omega)
  unfold numerator
  exact (differentiableAt_const _).div
    ((((((differentiableAt_id.add_const 1).mul (differentiableAt_id.add_const 2)).mul
      (differentiableAt_id.add_const 3)).mul (differentiableAt_id.add_const 4)).mul
      (differentiableAt_id.add_const 5)).mul (differentiableAt_id.add_const 6))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) h5) h6)

private theorem norm_kernel_le {s : ℂ} {d : ℝ} (hd : 0 < d)
    (h0 : d ≤ ‖s‖) (h1 : d ≤ ‖s + 1‖) (h2 : d ≤ ‖s + 2‖)
    (h3 : d ≤ ‖s + 3‖) (h4 : d ≤ ‖s + 4‖) (h5 : d ≤ ‖s + 5‖) (h6 : d ≤ ‖s + 6‖) :
    ‖kernel s‖ ≤ 1 / d ^ 7 := by
  have hp : d ^ 7 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ := by
    calc
      d ^ 7 = d * d * d * d * d * d * d := by ring
      _ ≤ _ := by gcongr
  simpa only [kernel, norm_div, norm_one, norm_mul] using
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (pow_pos hd 7) hp

private theorem factor_lower (σ t : ℝ) (hσ : σ = -1 / 2 ∨ σ = 3 / 2)
    (n : ℕ) (hn : n ≤ 6) :
    (1 + |t|) / 3 ≤ ‖((σ : ℂ) + t * I) + n‖ := by
  have hreal : (1 / 2 : ℝ) ≤ |σ + n| := by
    rcases hσ with rfl | rfl <;> interval_cases n <;> norm_num
  have hr := Complex.abs_re_le_norm (((σ : ℂ) + t * I) + n)
  have hi := Complex.abs_im_le_norm (((σ : ℂ) + t * I) + n)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, natCast_re] at hr
  simp only [add_im, ofReal_im, ofReal_re, mul_im, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add, natCast_im] at hi
  linarith

/-- A uniform fifth-power bound on the two vertical lines and the strip's horizontal sides
(the kernel actually decays like the seventh power). The constant is coarse. -/
theorem decayFive_kernel : DecayFive kernel 2187 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro σ hσ
    have hn (n : ℕ) (hn : n ≤ 6) (t : ℝ) :
        ((σ : ℂ) + t * I) + n ≠ 0 := by
      apply norm_pos_iff.mp
      exact lt_of_lt_of_le (by positivity) (factor_lower σ t hσ n hn)
    unfold kernel
    refine continuous_const.div (by fun_prop) (fun t => ?_)
    have h0 : ((σ : ℂ) + t * I) ≠ 0 := by simpa using hn 0 (by omega) t
    have h1 : ((σ : ℂ) + t * I) + 1 ≠ 0 := by simpa using hn 1 (by omega) t
    have h2 : ((σ : ℂ) + t * I) + 2 ≠ 0 := by simpa using hn 2 (by omega) t
    have h3 : ((σ : ℂ) + t * I) + 3 ≠ 0 := by simpa using hn 3 (by omega) t
    have h4 : ((σ : ℂ) + t * I) + 4 ≠ 0 := by simpa using hn 4 (by omega) t
    have h5 : ((σ : ℂ) + t * I) + 5 ≠ 0 := by simpa using hn 5 (by omega) t
    have h6 : ((σ : ℂ) + t * I) + 6 ≠ 0 := by simpa using hn 6 (by omega) t
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero h0 h1) h2) h3) h4) h5) h6
  · intro σ hσ t
    have hn (n : ℕ) (hn : n ≤ 6) := factor_lower σ t hσ n hn
    have h := norm_kernel_le (s := (σ : ℂ) + t * I)
      (d := (1 + |t|) / 3) (by positivity)
      (by simpa using hn 0 (by omega))
      (by simpa using hn 1 (by omega))
      (by simpa using hn 2 (by omega))
      (by simpa using hn 3 (by omega))
      (by simpa using hn 4 (by omega))
      (by simpa using hn 5 (by omega))
      (by simpa using hn 6 (by omega))
    refine h.trans ?_
    have hp : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have he : 1 / ((1 + |t|) / 3) ^ 7 = 2187 / (1 + |t|) ^ 7 := by
      field_simp
      norm_num
    rw [he]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ hp (by norm_num))
  · intro s _ _ ht
    have hn (n : ℕ) : |s.im| ≤ ‖s + n‖ := by
      simpa using Complex.abs_im_le_norm (s + n)
    have h := norm_kernel_le (s := s) (d := |s.im|) (by linarith)
      (by simpa using hn 0) (by simpa using hn 1) (by simpa using hn 2)
      (by simpa using hn 3) (by simpa using hn 4) (by simpa using hn 5)
      (by simpa using hn 6)
    refine h.trans ?_
    calc
      1 / |s.im| ^ 7 ≤ 1 / |s.im| ^ 5 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_right₀ ht (by norm_num))
      _ ≤ 2187 / |s.im| ^ 5 := by gcongr; norm_num

/-- The sixfold kernel's explicit formula, retaining its left remainder. -/
theorem explicit_formula_sextic_at_heights {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ}
    (hd : LDatum f B D CR) (hf0 : f 0 ≠ 0) {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hT : GoodHeights f B T) :
    Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
      (kernel u * (x : ℂ) ^ u)) atTop
      (𝓝 ((1 / (2 * π) : ℂ) *
        ((∫ y : ℝ, contourIntegrand f kernel x (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, contourIntegrand f kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)) -
        logDeriv f 0 / 720)) := by
  have hM : DecayFive (fun s => numerator s / s) 2187 := by
    simpa only [← kernel_eq_numerator_div] using decayFive_kernel
  simpa only [← kernel_eq_numerator_div, numerator_zero, mul_one_div] using
    explicit_formula_pole_zero_at_heights hd hf0
      (fun _ hs => differentiableAt_numerator hs) hM hx hT

/-- Existential version of the sextic formula. -/
theorem explicit_formula_sextic {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ}
    (hd : LDatum f B D CR) (hf0 : f 0 ≠ 0) {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
        (kernel u * (x : ℂ) ^ u)) atTop
        (𝓝 ((1 / (2 * π) : ℂ) *
          ((∫ y : ℝ, contourIntegrand f kernel x (((3 / 2 : ℝ) : ℂ) + y * I)) -
            ∫ y : ℝ, contourIntegrand f kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)) -
          logDeriv f 0 / 720)) := by
  have hM : DecayFive (fun s => numerator s / s) 2187 := by
    simpa only [← kernel_eq_numerator_div] using decayFive_kernel
  simpa only [← kernel_eq_numerator_div, numerator_zero, mul_one_div] using
    explicit_formula_pole_zero hd hf0 (fun _ hs => differentiableAt_numerator hs) hM hx

/-! ## The prime sum is the sixth primitive of psi -/

/-- Compact support reduces the smoothed prime sum to its finite range. -/
theorem SsumG_sextic_eq_finite {x : ℝ} (hx : 0 < x) :
    SsumG (1 : DirichletCharacter ℂ 1) weight x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (Λ n : ℂ) * weight (n / x) := by
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  unfold SsumG
  simp only [hchar, mul_one]
  apply tsum_eq_sum
  intro n hn
  have hnf : ⌊x⌋₊ < n := by
    simp only [Finset.mem_Icc, Nat.zero_le, true_and] at hn
    omega
  have hxn : x < n := (Nat.floor_lt hx.le).1 hnf
  have hratio : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).2 (by simpa using hxn.le)
  rw [weight_eq_zero_of_one_le hratio, mul_zero]

/-- Scaling the sextic weight recovers the truncated-power primitive. -/
theorem scaled_weight_eq_sexticPrimitive {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (x : ℂ) ^ 6 * weight (a / x) = (sexticPrimitive (x - a) : ℂ) := by
  have hmax : x * max (1 - a / x) 0 = max (x - a) 0 := by
    rw [mul_max_of_nonneg _ _ hx.le, mul_zero]
    congr 1
    field_simp [hx.ne'] <;> ring
  have hre : x ^ 6 * ((max (1 - a / x) 0) ^ 6 / 720) =
      sexticPrimitive (x - a) := by
    rw [sexticPrimitive, ← hmax, mul_pow]
    ring
  unfold weight
  exact_mod_cast hre

/-- The exact conversion from the Mellin smoothed prime sum to `Psi6`. -/
theorem pow_six_mul_SsumG_sextic_eq_Psi6 {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ 6 * SsumG (1 : DirichletCharacter ℂ 1) weight x =
      (Psi6 x : ℂ) := by
  rw [SsumG_sextic_eq_finite hx, mul_sum]
  unfold Psi6 psi6Trunc
  push_cast
  apply sum_congr rfl
  intro n _
  calc
    (x : ℂ) ^ 6 * ((Λ n : ℂ) * weight (n / x)) =
        (Λ n : ℂ) * ((x : ℂ) ^ 6 * weight (n / x)) := by ring
    _ = (Λ n : ℂ) * (sexticPrimitive (x - n) : ℂ) := by
      rw [scaled_weight_eq_sexticPrimitive hx]

/-! ## The zeta version -/

theorem prime_sum_eq_right_line {x : ℝ} (hx : 0 < x) :
    SsumG (1 : DirichletCharacter ℂ 1) weight x =
      -(1 / (2 * π) : ℂ) *
        ∫ t : ℝ, contourIntegrand riemannZeta kernel x (((3 / 2 : ℝ) : ℂ) + t * I) := by
  have hline : (fun t : ℝ => mellin weight (((3 / 2 : ℝ) : ℂ) + t * I)) =
      fun t : ℝ => kernel (((3 / 2 : ℝ) : ℂ) + t * I) := by
    funext t
    exact mellin_weight (by simp)
  have hc : Continuous (fun t : ℝ => mellin weight (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [hline]
    exact decayFive_kernel.continuous_line _ (Or.inr rfl)
  have hi : Integrable (fun t : ℝ => mellin weight (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [hline]
    exact decayFive_kernel.integrable_line (Or.inr rfl)
  have hS := PolynomialPrimeSum.SsumG_eq_line (1 : DirichletCharacter ℂ 1)
    (fun _ _ => continuous_weight.continuousAt)
    (mellinConvergent_weight (by norm_num)) hc hi hx
  have hF (t : ℝ) : Fline (1 : DirichletCharacter ℂ 1) weight x
      (((3 / 2 : ℝ) : ℂ) + t * I) =
      -contourIntegrand riemannZeta kernel x (((3 / 2 : ℝ) : ℂ) + t * I) := by
    rw [Fline, contourIntegrand, LFunction_one_mod_one, logDeriv_apply,
      mellin_weight (by simp)]
    ring
  simpa only [hF, integral_neg, mul_neg, neg_mul] using hS

private theorem contourIntegrand_zetaF_eq (x : ℝ) {s : ℂ}
    (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    contourIntegrand zetaF kernel x s =
      contourIntegrand (fun z : ℂ => z - 1) kernel x s +
        contourIntegrand riemannZeta kernel x s := by
  rw [contourIntegrand, contourIntegrand, contourIntegrand,
    logDeriv_zetaF_eq hs hz, logDeriv_sub_one]
  ring

/-- The sextic Mellin kernel gives a zero-sum formula with the constant at zero evaluated and
the left vertical remainder retained. -/
theorem explicit_formula_zeta_sextic_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        (kernel u * (x : ℂ) ^ u)) atTop
        (𝓝 ((x : ℂ) / 5040 - SsumG (1 : DirichletCharacter ℂ 1) weight x -
          (1 / (2 * π) : ℂ) *
            (∫ y : ℝ, contourIntegrand riemannZeta kernel x
              (((-1 / 2 : ℝ) : ℂ) + y * I)) - Complex.log (2 * π) / 720)) := by
  have hz0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hf0 : zetaF 0 ≠ 0 := by
    rw [zetaF_of_ne (by norm_num), riemannZeta_zero]
    norm_num
  have hlim := explicit_formula_sextic_at_heights ldatum_zeta hf0 hx hT
  obtain ⟨T', hT', hlim1⟩ := explicit_formula_sextic ldatum_sub_one (by norm_num) hx
  have hconst : ∀ k, ∑ u ∈ zerosRectD (fun s : ℂ => s - 1) (T' k),
      (multRectD (fun s : ℂ => s - 1) (T' k) u : ℂ) *
        (kernel u * (x : ℂ) ^ u) = (x : ℂ) / 5040 := by
    intro k
    have hpos : 0 < T' k := by
      linarith [(hT' k).1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [sum_zerosRect_sub_one hpos, Complex.cpow_one]
    norm_num [kernel]
    ring
  simp_rw [hconst] at hlim1
  have hmain := tendsto_nhds_unique tendsto_const_nhds hlim1
  have hR1 : ∀ y : ℝ, ((3 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  have hL1 : ∀ y : ℝ, ((-1 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  have hRz : ∀ y : ℝ, riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
  have hLz : ∀ y : ℝ, riemannZeta (((-1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    zeta_ne_zero_of_zetaF (hL1 y)
      (zetaF_ne_zero_strip (by simp; norm_num) (by simp; norm_num))
  have iR := integrable_contour_right ldatum_zeta decayFive_kernel hx
  have iL := integrable_contour_left ldatum_zeta decayFive_kernel hx
  have iR1 := integrable_contour_right ldatum_sub_one decayFive_kernel hx
  have iL1 := integrable_contour_left ldatum_sub_one decayFive_kernel hx
  set A := ∫ y : ℝ, contourIntegrand zetaF kernel x (((3 / 2 : ℝ) : ℂ) + y * I) with hA
  set A1 := ∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) kernel x
    (((3 / 2 : ℝ) : ℂ) + y * I) with hA1
  set Bv := ∫ y : ℝ, contourIntegrand zetaF kernel x (((-1 / 2 : ℝ) : ℂ) + y * I) with hBv
  set B1v := ∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) kernel x
    (((-1 / 2 : ℝ) : ℂ) + y * I) with hB1v
  have IR : ∫ y : ℝ, contourIntegrand riemannZeta kernel x
      (((3 / 2 : ℝ) : ℂ) + y * I) = A - A1 := by
    rw [hA, hA1, ← integral_sub iR iR1]
    congr 1
    ext y
    rw [contourIntegrand_zetaF_eq x (hR1 y) (hRz y)]
    ring
  have IL : ∫ y : ℝ, contourIntegrand riemannZeta kernel x
      (((-1 / 2 : ℝ) : ℂ) + y * I) = Bv - B1v := by
    rw [hBv, hB1v, ← integral_sub iL iL1]
    congr 1
    ext y
    rw [contourIntegrand_zetaF_eq x (hL1 y) (hLz y)]
    ring
  have hS := prime_sum_eq_right_line hx
  rw [IR] at hS
  have hzero : logDeriv zetaF 0 = logDeriv (fun s : ℂ => s - 1) 0 +
      Complex.log (2 * π) := by
    rw [logDeriv_zetaF_eq (by norm_num) hz0, logDeriv_sub_one,
      PolynomialZeta.logDeriv_riemannZeta_zero]
  convert hlim using 2
  rw [hmain, hS, IL, hzero]
  ring

/-- The unevaluated left vertical contribution to the sixth primitive. -/
noncomputable def psi6LeftRemainder (x : ℝ) : ℂ :=
  (x : ℂ) ^ 6 / (2 * π) *
    ∫ y : ℝ, contourIntegrand riemannZeta kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)

/-- The fixed-strip explicit formula written for the actual sixfold primitive
`Psi6 x = ∑ Λ(n) (x-n)_+^6/720`. -/
theorem explicit_formula_Psi6_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        ((x : ℂ) ^ (u + 6) /
          (u * (u + 1) * (u + 2) * (u + 3) * (u + 4) * (u + 5) * (u + 6)))) atTop
        (𝓝 ((x : ℂ) ^ 7 / 5040 - (Psi6 x : ℂ) - psi6LeftRemainder x -
          (x : ℂ) ^ 6 * Complex.log (2 * π) / 720)) := by
  have hlim := explicit_formula_zeta_sextic_at_heights hT hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsum (k : ℕ) :
      (x : ℂ) ^ 6 * (∑ u ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) u : ℂ) * (kernel u * (x : ℂ) ^ u)) =
      ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        ((x : ℂ) ^ (u + 6) /
          (u * (u + 1) * (u + 2) * (u + 3) * (u + 4) * (u + 5) * (u + 6))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Complex.cpow_add _ _ hx0, Complex.cpow_ofNat]
    unfold kernel
    ring
  have hscaled := hlim.const_mul ((x : ℂ) ^ 6)
  simp_rw [hsum] at hscaled
  simp only [mul_sub] at hscaled
  rw [pow_six_mul_SsumG_sextic_eq_Psi6 hx] at hscaled
  convert hscaled using 2 <;> unfold psi6LeftRemainder <;> ring

end TernaryGoldbach.RSBounds.SchoenfeldSexticExplicit
