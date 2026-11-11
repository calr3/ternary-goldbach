import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic
import RSBounds.PolynomialPsi
import TernaryGoldbach.Explicit.ExplicitFormula
import RSBounds.QuadraticContourLimit
import RSBounds.PolynomialLowerKernel
import RSBounds.QuadraticSubOne
import RSBounds.PolynomialZetaFormula
import RSBounds.PolynomialPrimeSum
import TernaryGoldbach.Explicit.ZetaExplicit
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Consolidated quadratic smoothing kernel and actual explicit formula

Verification is recorded by the matching exact-source runner and axiom audit.
The original draft files are preserved untouched. Already checked results are
imported; their declarations are not reproduced. Separate sections retain each
draft's namespace and local open-command scope.
-/

/-! ## Preserved draft: `RSBounds/QuadraticMellin.lean` -/
section QuadraticMellinDraft

/-!
# Mellin transform for twice-integrated polynomial smoothing

The weight `(1-u)_+²/2` has Mellin transform `1/(s(s+1)(s+2))`
on `Re s>0`. The rational kernel is its meromorphic continuation outside
that half-plane. This is the `m=2` kernel used in Schoenfeld's second paper.
The proof specializes Mathlib's Mellin transform of powers on `(0,1]`.
-/

open Complex Set MeasureTheory

namespace TernaryGoldbach.RSBounds.QuadraticMellin

noncomputable def weight (u : ℝ) : ℂ :=
  (((max (1 - u) 0) ^ 2 / 2 : ℝ) : ℂ)

noncomputable def kernel (s : ℂ) : ℂ := 1 / (s * (s + 1) * (s + 2))

theorem continuous_weight : Continuous weight := by
  unfold weight
  fun_prop

theorem weight_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) : weight u = 0 := by
  simp [weight, max_eq_right (sub_nonpos.mpr hu)]

private theorem hasMellin_congr_pos {f g : ℝ → ℂ} {s a : ℂ}
    (hfg : ∀ u : ℝ, 0 < u → f u = g u) (hf : HasMellin f s a) :
    HasMellin g s a := by
  constructor
  · exact (integrableOn_congr_fun
      (fun (u : ℝ) hu => congrArg (fun z : ℂ => (u : ℂ) ^ (s - 1) • z) (hfg u hu))
      measurableSet_Ioi).mp hf.1
  · calc
      mellin g s = mellin f s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        change (u : ℂ) ^ (s - 1) • g u = (u : ℂ) ^ (s - 1) • f u
        rw [hfg u hu]
      _ = a := hf.2

private theorem hasMellin_add_values {f g : ℝ → ℂ} {s a b : ℂ}
    (hf : HasMellin f s a) (hg : HasMellin g s b) :
    HasMellin (fun u => f u + g u) s (a + b) := by
  simpa only [hf.2, hg.2] using hasMellin_add hf.1 hg.1

private theorem hasMellin_sub_values {f g : ℝ → ℂ} {s a b : ℂ}
    (hf : HasMellin f s a) (hg : HasMellin g s b) :
    HasMellin (fun u => f u - g u) s (a - b) := by
  simpa only [hf.2, hg.2] using hasMellin_sub hf.1 hg.1

private theorem hasMellin_mul_value {f : ℝ → ℂ} {s a : ℂ}
    (hf : HasMellin f s a) (c : ℂ) :
    HasMellin (fun u => c * f u) s (c * a) := by
  simpa only [smul_eq_mul, hf.2] using hasMellin_const_smul hf.1 c

private theorem shifted_ne_zero {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    s + n ≠ 0 := by
  have hpos : 0 < (s + n).re := by
    simp only [add_re, natCast_re]
    positivity
  intro h
  exact (ne_of_gt hpos) (congrArg Complex.re h)

theorem hasMellin_weight {s : ℂ} (hs : 0 < s.re) :
    HasMellin weight s (kernel s) := by
  let p : ℕ → ℝ → ℂ := fun n => indicator (Ioc 0 1) (fun u => (u : ℂ) ^ n)
  have hp (n : ℕ) : HasMellin (p n) s (1 / (s + n)) := by
    have hpos : 0 < s.re + (n : ℂ).re := by
      simp only [natCast_re]
      positivity
    simpa only [p, cpow_natCast] using hasMellin_cpow_Ioc (n : ℂ) hpos
  have hq := hasMellin_add_values
    (hasMellin_sub_values (hp 0) (hasMellin_mul_value (hp 1) 2)) (hp 2)
  have hdiv : HasMellin (fun u => (p 0 u - 2 * p 1 u + p 2 u) / 2) s
      ((1 / s - 2 * (1 / (s + 1)) + 1 / (s + 2)) / 2) := by
    refine ⟨hq.1.div_const 2, ?_⟩
    rw [mellin_div_const, hq.2]
    norm_num
  have hweight : HasMellin weight s
      ((1 / s - 2 * (1 / (s + 1)) + 1 / (s + 2)) / 2) := by
    refine hasMellin_congr_pos (fun u hu => ?_) hdiv
    by_cases hu1 : u ≤ 1
    · have hmem : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, hu1⟩
      simp only [p, indicator_of_mem hmem, weight,
        max_eq_left (sub_nonneg.mpr hu1)]
      push_cast
      ring
    · have hnmem : u ∉ Ioc (0 : ℝ) 1 := fun h => hu1 h.2
      have hle : 1 ≤ u := (lt_of_not_ge hu1).le
      simp [p, hnmem, weight_eq_zero_of_one_le hle]
  have h0 : s ≠ 0 := by simpa using shifted_ne_zero hs 0
  have h1 : s + 1 ≠ 0 := by simpa using shifted_ne_zero hs 1
  have h2 : s + 2 ≠ 0 := by simpa using shifted_ne_zero hs 2
  have heval : (1 / s - 2 * (1 / (s + 1)) + 1 / (s + 2)) / 2 = kernel s := by
    unfold kernel
    field_simp [h0, h1, h2]
    ring
  exact heval ▸ hweight

theorem mellinConvergent_weight {s : ℂ} (hs : 0 < s.re) : MellinConvergent weight s :=
  (hasMellin_weight hs).1

theorem mellin_weight {s : ℂ} (hs : 0 < s.re) : mellin weight s = kernel s :=
  (hasMellin_weight hs).2

end TernaryGoldbach.RSBounds.QuadraticMellin
end QuadraticMellinDraft

/-! ## Preserved draft: `RSBounds/QuadraticPsi.lean` -/
section QuadraticPsiDraft

/-!
# Twice-integrated polynomial smoothing of psi

This is the finite arithmetic smoothing with m=2. It reuses the existing
finite indicator representation of psi and proves the exact second-difference
identities, including prime-power endpoints. No zero assumption is used.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.QuadraticPsi

/-- The CDF of the sum of two unit intervals. -/
noncomputable def W (t : ℝ) : ℝ :=
  ((max t 0) ^ 2 - 2 * (max (t - 1) 0) ^ 2 + (max (t - 2) 0) ^ 2) / 2

theorem W_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : W t = 0 := by
  simp [W, max_eq_right ht, max_eq_right (show t - 1 ≤ 0 by linarith),
    max_eq_right (show t - 2 ≤ 0 by linarith)]

theorem W_eq_one_of_two_le {t : ℝ} (ht : 2 ≤ t) : W t = 1 := by
  rw [W, max_eq_left (by linarith : 0 ≤ t),
    max_eq_left (by linarith : 0 ≤ t - 1), max_eq_left (by linarith : 0 ≤ t - 2)]
  ring

theorem W_bounds (t : ℝ) : 0 ≤ W t ∧ W t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · rw [W_eq_zero_of_nonpos h0]
    norm_num
  have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge h0)
  by_cases h1 : t ≤ 1
  · rw [W, max_eq_left ht0, max_eq_right (by linarith : t - 1 ≤ 0),
      max_eq_right (by linarith : t - 2 ≤ 0)]
    constructor <;> nlinarith [sq_nonneg t,
      mul_nonneg ht0 (show 0 ≤ 1 - t by linarith)]
  have ht1 : 1 ≤ t := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : t ≤ 2
  · rw [W, max_eq_left ht0, max_eq_left (by linarith : 0 ≤ t - 1),
      max_eq_right (by linarith : t - 2 ≤ 0)]
    constructor <;> nlinarith [sq_nonneg (t - 2),
      mul_nonneg (show 0 ≤ t - 1 by linarith) (show 0 ≤ 2 - t by linarith)]
  · rw [W_eq_one_of_two_le (le_of_lt (lt_of_not_ge h2))]
    norm_num

theorem W_nonneg (t : ℝ) : 0 ≤ W t := (W_bounds t).1

theorem W_le_one (t : ℝ) : W t ≤ 1 := (W_bounds t).2

/-- The second truncated-power primitive of a point mass. -/
noncomputable def quadraticPrimitive (t : ℝ) : ℝ := (max t 0) ^ 2 / 2

/-- A common finite truncation of the second primitive of psi. -/
noncomputable def psi2Trunc (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * quadraticPrimitive (t - n)

/-- The canonical finite truncated-power primitive. -/
noncomputable def Psi2 (t : ℝ) : ℝ := psi2Trunc ⌊t⌋₊ t

/-- Forward second difference, before normalization by the step size. -/
def secondDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + 2 * h) - 2 * f (x + h) + f x

/-- Polynomial upper smoothing of psi. -/
noncomputable def psiUpper (N : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * W ((x + 2 * h - n) / h)

/-- Polynomial lower smoothing of psi. -/
noncomputable def psiLower (N : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * W ((x - n) / h)

/-- The lower smoothing never exceeds psi. -/
theorem psiLower_le_psi {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) : psiLower N x h ≤ Chebyshev.psi x := by
  rw [PolynomialPsi.psi_eq_indicator_sum hx hN]
  unfold psiLower
  apply sum_le_sum
  intro n _
  by_cases hn : (n : ℝ) ≤ x
  · rw [if_pos hn]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (W_le_one ((x - n) / h))
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · rw [if_neg hn, W_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (by linarith [lt_of_not_ge hn]) hh.le), mul_zero]

/-- The upper smoothing majorizes psi, including at prime-power jumps. -/
theorem psi_le_psiUpper {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) : Chebyshev.psi x ≤ psiUpper N x h := by
  rw [PolynomialPsi.psi_eq_indicator_sum hx hN]
  unfold psiUpper
  apply sum_le_sum
  intro n _
  by_cases hn : (n : ℝ) ≤ x
  · have hw : 2 ≤ (x + 2 * h - n) / h := (le_div_iff₀ hh).2 (by linarith)
    rw [if_pos hn, W_eq_one_of_two_le hw, mul_one]
  · rw [if_neg hn]
    exact mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (W_nonneg _)

/-- The two polynomial smoothings sandwich psi on one common truncation. -/
theorem psi_sandwich {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    psiLower N x h ≤ Chebyshev.psi x ∧ Chebyshev.psi x ≤ psiUpper N x h :=
  ⟨psiLower_le_psi hx hh (by linarith), psi_le_psiUpper hx hh (by linarith)⟩

/-- Terms beyond the common truncation have zero upper weight. -/
theorem upper_weight_eq_zero {x h : ℝ} (hh : 0 < h) {N n : ℕ}
    (hN : x + 2 * h ≤ N) (hn : N < n) : W ((x + 2 * h - n) / h) = 0 := by
  apply W_eq_zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hh.le
  have hn' : (N : ℝ) < n := by exact_mod_cast hn
  linarith

/-- A sufficiently large finite truncation equals the canonical primitive. -/
theorem psi2Trunc_eq_Psi2 {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : t ≤ N) :
    psi2Trunc N t = Psi2 t := by
  have hfloor : ⌊t⌋₊ ≤ N := by exact_mod_cast (Nat.floor_le ht).trans hN
  unfold Psi2 psi2Trunc
  symm
  apply sum_subset (Icc_subset_Icc le_rfl hfloor)
  intro n hn hn'
  have hnf : ⌊t⌋₊ < n := by
    have hn0 : 0 ≤ n := Nat.zero_le n
    simp only [mem_Icc, hn0, true_and] at hn'
    omega
  have hnt : t < n := (Nat.floor_lt ht).1 hnf
  simp [quadraticPrimitive, max_eq_right (show t - n ≤ 0 by linarith)]

/-- Second differences commute with finite sums. -/
theorem secondDifference_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (x h : ℝ) :
    secondDifference (fun t => ∑ i ∈ s, f i t) x h =
      ∑ i ∈ s, secondDifference (f i) x h := by
  simp only [secondDifference, sum_add_distrib, sum_sub_distrib, mul_sum]

/-- Second differences commute with scalar multiplication. -/
theorem secondDifference_mul (c : ℝ) (f : ℝ → ℝ) (x h : ℝ) :
    secondDifference (fun t => c * f t) x h = c * secondDifference f x h := by
  unfold secondDifference
  ring

/-- The normalized second difference of one truncated power is the quadratic
CDF weight. This is a purely algebraic identity. -/
theorem secondDifference_quadraticPrimitive {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    secondDifference (fun t => quadraticPrimitive (t - a)) x h / h ^ 2 =
      W ((x + 2 * h - a) / h) := by
  have hd (t : ℝ) : max (t / h) 0 = max t 0 / h := by
    simpa only [zero_div] using max_div_div_right hh.le t 0
  have e1 : (x + 2 * h - a) / h - 1 = (x + h - a) / h := by
    field_simp [hh.ne']; ring
  have e2 : (x + 2 * h - a) / h - 2 = (x - a) / h := by
    field_simp [hh.ne']; ring
  unfold secondDifference quadraticPrimitive W
  rw [e1, e2]
  simp only [hd, div_pow]
  ring

/-- The normalized forward difference of the finite second primitive is
exactly the upper polynomial smoothing. -/
theorem secondDifference_psi2Trunc {h : ℝ} (hh : 0 < h) (N : ℕ) (x : ℝ) :
    secondDifference (psi2Trunc N) x h / h ^ 2 = psiUpper N x h := by
  unfold psi2Trunc psiUpper
  rw [secondDifference_sum, sum_div]
  apply sum_congr rfl
  intro n _
  rw [secondDifference_mul, mul_div_assoc,
    secondDifference_quadraticPrimitive hh]

/-- The canonical second primitive has the same difference identity whenever
the finite upper sum contains its complete support. -/
theorem secondDifference_Psi2 {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    secondDifference Psi2 x h / h ^ 2 = psiUpper N x h := by
  have h0 := psi2Trunc_eq_Psi2 hx (show x ≤ N by linarith)
  have h1 := psi2Trunc_eq_Psi2 (show 0 ≤ x + h by linarith)
    (show x + h ≤ N by linarith)
  have h2 := psi2Trunc_eq_Psi2 (show 0 ≤ x + 2 * h by linarith) hN
  have hd : secondDifference Psi2 x h = secondDifference (psi2Trunc N) x h := by
    unfold secondDifference
    rw [h0, h1, h2]
  rw [hd]
  exact secondDifference_psi2Trunc hh N x

/-- The backward-shifted forward difference is exactly the lower smoothing. -/
theorem secondDifference_Psi2_lower {x h : ℝ} (hh : 0 < h) (hx : 2 * h ≤ x)
    {N : ℕ} (hN : x ≤ N) :
    secondDifference Psi2 (x - 2 * h) h / h ^ 2 = psiLower N x h := by
  have ht := secondDifference_Psi2 (x := x - 2 * h) (by linarith) hh
    (show x - 2 * h + 2 * h ≤ N by linarith)
  simpa only [psiUpper, psiLower, sub_add_cancel] using ht

/-- Once the two polynomial smoothings have controlled errors, the cost of
unsmoothing is precisely `h`. The analytic error bound remains explicit. -/
theorem psi_error_of_polynomial_errors {x h E : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N)
    (hupper : |psiUpper N x h - (x + h)| ≤ E)
    (hlower : |psiLower N x h - (x - h)| ≤ E) :
    |Chebyshev.psi x - x| ≤ E + h := by
  obtain ⟨hlo, hup⟩ := psi_sandwich hx hh hN
  obtain ⟨hu1, hu2⟩ := abs_le.mp hupper
  obtain ⟨hl1, hl2⟩ := abs_le.mp hlower
  rw [abs_le]
  constructor <;> linarith

end TernaryGoldbach.RSBounds.QuadraticPsi
end QuadraticPsiDraft

/-! ## Preserved draft: `RSBounds/QuadraticPsiMellin.lean` -/
section QuadraticPsiMellinDraft
/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/

/-!
# The quadratic smoothed prime sum is the second primitive of psi

This is the arithmetic bridge between the canonical truncated-power sum
`QuadraticPsi.Psi2` and the Mellin-transform formulation. Compact support
makes the prime sum finite. No zero-location or analytic prime estimate is
assumed.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.QuadraticPsiMellin

open TernaryGoldbach.Explicit QuadraticPsi QuadraticMellin

/-- Compact support reduces the smoothed prime sum to its finite range. -/
theorem SsumG_quadratic_eq_finite {x : ℝ} (hx : 0 < x) :
    SsumG (1 : DirichletCharacter ℂ 1) weight x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (Λ n : ℂ) * weight (n / x) := by
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  unfold SsumG
  simp only [hchar, mul_one]
  apply tsum_eq_sum
  intro n hn
  have hnf : ⌊x⌋₊ < n := by
    simp only [mem_Icc, Nat.zero_le, true_and] at hn
    omega
  have hxn : x < n := (Nat.floor_lt hx.le).1 hnf
  have hratio : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).2 (by simpa using hxn.le)
  rw [weight_eq_zero_of_one_le hratio, mul_zero]

/-- Scaling the quadratic weight recovers the truncated-power primitive. -/
theorem scaled_weight_eq_quadraticPrimitive {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (x : ℂ) ^ 2 * weight (a / x) = (quadraticPrimitive (x - a) : ℂ) := by
  have hmax : x * max (1 - a / x) 0 = max (x - a) 0 := by
    rw [mul_max_of_nonneg _ _ hx.le, mul_zero]
    congr 1
    field_simp [hx.ne'] <;> ring
  have hre : x ^ 2 * ((max (1 - a / x) 0) ^ 2 / 2) =
      quadraticPrimitive (x - a) := by
    rw [quadraticPrimitive, ← hmax, mul_pow]
    ring
  unfold weight
  exact_mod_cast hre

/-- The exact conversion from the Mellin smoothed prime sum to `Psi2`. -/
theorem pow_two_mul_SsumG_quadratic_eq_Psi2 {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ 2 * SsumG (1 : DirichletCharacter ℂ 1) weight x =
      (Psi2 x : ℂ) := by
  rw [SsumG_quadratic_eq_finite hx, mul_sum]
  unfold Psi2 psi2Trunc
  push_cast
  apply sum_congr rfl
  intro n _
  calc
    (x : ℂ) ^ 2 * ((Λ n : ℂ) * weight (n / x)) =
        (Λ n : ℂ) * ((x : ℂ) ^ 2 * weight (n / x)) := by ring
    _ = (Λ n : ℂ) * (quadraticPrimitive (x - n) : ℂ) := by
      rw [scaled_weight_eq_quadraticPrimitive hx]

end TernaryGoldbach.RSBounds.QuadraticPsiMellin
end QuadraticPsiMellinDraft

/-! ## Preserved draft: `RSBounds/QuadraticKernel.lean` -/
section QuadraticKernelDraft

/-!
# The twice-integrated kernel in the existing contour theorem

The numerator `1/((s+1)(s+2))` is holomorphic on `Re s>-1`.
Its quotient by `s` satisfies the already established degree-two contour
hypotheses. No new contour argument or zero-location premise is used.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.QuadraticKernel

open TernaryGoldbach.Explicit PolynomialExplicit QuadraticMellin QuadraticContourLimit

noncomputable def numerator (s : ℂ) : ℂ := 1 / ((s + 1) * (s + 2))

theorem kernel_eq_numerator_div (s : ℂ) : kernel s = numerator s / s := by
  simp only [kernel, numerator, div_div]
  congr 1
  ring

theorem numerator_zero : numerator 0 = 1 / 2 := by norm_num [numerator]

theorem numerator_one : numerator 1 = 1 / 6 := by norm_num [numerator]

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
  unfold numerator
  exact (differentiableAt_const _).div
    ((differentiableAt_id.add_const 1).mul (differentiableAt_id.add_const 2))
    (mul_ne_zero h1 h2)

private theorem norm_kernel_le {s : ℂ} {d : ℝ} (hd : 0 < d)
    (h0 : d ≤ ‖s‖) (h1 : d ≤ ‖s + 1‖) (h2 : d ≤ ‖s + 2‖) :
    ‖kernel s‖ ≤ 1 / d ^ 3 := by
  have hp : d ^ 3 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ := by
    calc
      d ^ 3 = d * d * d := by ring
      _ ≤ _ := by gcongr
  simpa only [kernel, norm_div, norm_one, norm_mul] using
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (pow_pos hd 3) hp

private theorem factor_lower (σ t : ℝ) (hσ : σ = -1 / 2 ∨ σ = 3 / 2)
    (n : ℕ) (hn : n ≤ 2) :
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

theorem norm_kernel_line_le_cube (σ t : ℝ) (hσ : σ = -1 / 2 ∨ σ = 3 / 2) :
    ‖kernel ((σ : ℂ) + t * I)‖ ≤ 27 / (1 + |t|) ^ 3 := by
  have hn (n : ℕ) (hn : n ≤ 2) := factor_lower σ t hσ n hn
  have h := norm_kernel_le (s := (σ : ℂ) + t * I)
    (d := (1 + |t|) / 3) (by positivity)
    (by simpa using hn 0 (by omega))
    (by simpa using hn 1 (by omega))
    (by simpa using hn 2 (by omega))
  refine h.trans_eq ?_
  have hp : 1 + |t| ≠ 0 := by positivity
  field_simp [hp]
  <;> ring

theorem decayTwo_kernel : DecayTwo kernel 27 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro σ hσ
    have hn (n : ℕ) (hn : n ≤ 2) (t : ℝ) :
        ((σ : ℂ) + t * I) + n ≠ 0 := by
      apply norm_pos_iff.mp
      exact lt_of_lt_of_le (by positivity) (factor_lower σ t hσ n hn)
    unfold kernel
    refine continuous_const.div (by fun_prop) (fun t => ?_)
    have h0 : ((σ : ℂ) + t * I) ≠ 0 := by simpa using hn 0 (by omega) t
    have h1 : ((σ : ℂ) + t * I) + 1 ≠ 0 := by simpa using hn 1 (by omega) t
    have h2 : ((σ : ℂ) + t * I) + 2 ≠ 0 := by simpa using hn 2 (by omega) t
    exact mul_ne_zero (mul_ne_zero h0 h1) h2
  · intro σ hσ t
    refine (norm_kernel_line_le_cube σ t hσ).trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h := mul_nonneg (sq_nonneg (1 + |t|)) (abs_nonneg t)
    nlinarith
  · intro s _ _ ht
    have hn (n : ℕ) : |s.im| ≤ ‖s + n‖ := by
      simpa using Complex.abs_im_le_norm (s + n)
    have h := norm_kernel_le (s := s) (d := |s.im|) (by linarith)
      (by simpa using hn 0) (by simpa using hn 1) (by simpa using hn 2)
    refine h.trans ?_
    have hd : 0 < |s.im| := by linarith
    have he : 1 / |s.im| ^ 3 ≤ 1 / |s.im| ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith [mul_nonneg (sq_nonneg |s.im|) (show 0 ≤ |s.im| - 1 by linarith)]
    exact he.trans (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _))

/-- The actual-zeta entire-factor formula for the quadratic weight. -/
theorem explicit_formula_zetaF_at_heights {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hT : GoodHeights zetaF BPz2 T) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
      (kernel u * (x : ℂ) ^ u)) atTop
      (𝓝 ((1 / (2 * π) : ℂ) *
        ((∫ y : ℝ, contourIntegrand zetaF kernel x (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, contourIntegrand zetaF kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)) -
        logDeriv zetaF 0 / 2)) := by
  have hM : DecayTwo (fun s => numerator s / s) 27 := by
    simpa only [← kernel_eq_numerator_div] using decayTwo_kernel
  simpa only [← kernel_eq_numerator_div, numerator_zero, mul_one_div] using
    QuadraticContourLimit.explicit_formula_pole_zero_at_heights
      (fun _ hs => differentiableAt_numerator hs) hM hx hT

end TernaryGoldbach.RSBounds.QuadraticKernel
end QuadraticKernelDraft

/-! ## Preserved draft: `RSBounds/QuadraticZeroKernel.lean` -/
section QuadraticZeroKernelDraft

/-!
# Actual second-difference zero coefficients

The integration identities and affine integral bound are reused from
`PolynomialZeroKernel` at n=2. The high coefficient retains the exact
polynomial R₂(δ)=((1+δ)^3+1)^2. No zero-location hypothesis is used beyond
explicit inequalities on the supplied complex argument.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace TernaryGoldbach.RSBounds.QuadraticZeroKernel

open PolynomialZeroKernel

theorem forwardDiff_two (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    forwardDiff h 2 f x = f (x + 2 * h) - 2 * f (x + h) + f x := by
  simp only [forwardDiff]
  rw [show x + h + h = x + 2 * h by ring]
  ring

/-- The repeated integral is exactly the finite difference of the second antiderivative. -/
theorem zero_term_twofold_identity {ρ : ℂ} (hρ : 0 < ρ.re)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    iteratedIntegral h 2 (fun t => (t : ℂ) ^ ρ / ρ) x =
      forwardDiff h 2 (antiderivative ρ 2) x := by
  have hz : antiderivative ρ 0 = fun t : ℝ => (t : ℂ) ^ ρ / ρ := by
    funext t
    simp [antiderivative, rising]
  have hc : ∀ x, 0 < x → ContinuousAt (antiderivative ρ 0) x := by
    intro x hx
    have hr : ρ ≠ 0 := by simpa using add_nat_ne_zero hρ 0
    rw [hz]
    exact ((hasDerivAt_ofReal_cpow_const hx.ne' hr).div_const ρ).continuousAt
  simpa only [hz] using
    iteratedIntegral_eq_forwardDiff hh (antiderivative ρ)
      (fun n x hx => antiderivative_hasDerivAt hρ n hx) hc 2 x hx

/-- The low-zero estimate, before dividing by the smoothing volume `h^2`. -/
theorem norm_second_difference_le_low {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖forwardDiff h 2 (antiderivative ρ 2) x‖ ≤
      h ^ 2 * (x ^ ρ.re / ‖ρ‖) * (1 + h / x) := by
  rw [← zero_term_twofold_identity hρ hx hh]
  have hf : ∀ t, x ≤ t → ‖(t : ℂ) ^ ρ / ρ‖ ≤ 0 + (x ^ ρ.re / (x * ‖ρ‖)) * t := by
    intro t ht
    simpa only [zero_add] using norm_zero_term_le_affine hρ hρ1 hx ht
  have hm := norm_iteratedIntegral_le_affine hh (fun t => (t : ℂ) ^ ρ / ρ)
    0 (x ^ ρ.re / (x * ‖ρ‖)) 2 x hf
  have hn : ρ ≠ 0 := by simpa using add_nat_ne_zero hρ 0
  have hn0 : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  refine hm.trans_eq ?_
  norm_num
  field_simp [hx.ne', hn0] <;> ring

theorem norm_normalized_second_difference_le_low {ρ : ℂ}
    (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖forwardDiff h 2 (antiderivative ρ 2) x / (h : ℂ) ^ 2‖ ≤
      (x ^ ρ.re / ‖ρ‖) * (1 + h / x) := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
    div_le_iff₀ (pow_pos hh 2)]
  have hm := norm_second_difference_le_low hρ hρ1 hx hh.le
  nlinarith

/-- The dimensionless second-difference numerator. -/
noncomputable def numerator (δ : ℝ) (ρ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 3,
    (-1 : ℂ) ^ j * (Nat.choose 2 j : ℂ) * ((1 + (j : ℝ) * δ : ℝ) : ℂ) ^ (ρ + 2)

/-- The normalized zero coefficient for the upper twofold average. -/
noncomputable def upperKernel (δ : ℝ) (ρ : ℂ) : ℂ :=
  numerator δ ρ / ((δ : ℂ) ^ 2 * rising ρ 2)

def R2 (δ : ℝ) : ℝ := ((1 + δ) ^ 3 + 1) ^ 2

theorem upperKernel_eq_normalized_difference (δ : ℝ) (ρ : ℂ) :
    upperKernel δ ρ = forwardDiff δ 2 (antiderivative ρ 2) 1 / (δ : ℂ) ^ 2 := by
  simp only [upperKernel, numerator, forwardDiff_two, antiderivative]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- The exact low-zero factor for m=2. -/
theorem norm_upperKernel_le_low {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (hρ : 0 < ρ.re) (hρ1 : ρ.re ≤ 1) :
    ‖upperKernel δ ρ‖ ≤ (1 + δ) / ‖ρ‖ := by
  rw [upperKernel_eq_normalized_difference]
  have hm := norm_normalized_second_difference_le_low hρ hρ1 (by norm_num : (0 : ℝ) < 1) hδ
  simpa only [Real.one_rpow, one_div, div_one, inv_one, one_mul, mul_one, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hm

theorem norm_numerator_le_R2 {δ : ℝ} (hδ : 0 ≤ δ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    ‖numerator δ ρ‖ ≤ R2 δ := by
  have hterm (j : ℕ) :
      ‖(-1 : ℂ) ^ j * (Nat.choose 2 j : ℂ) *
          ((1 + (j : ℝ) * δ : ℝ) : ℂ) ^ (ρ + 2)‖ ≤
        (Nat.choose 2 j : ℝ) * (((1 + δ) ^ 3) ^ j) := by
    have hb : 1 ≤ 1 + (j : ℝ) * δ := by
      linarith [mul_nonneg (Nat.cast_nonneg j) hδ]
    have hb0 : 0 < 1 + (j : ℝ) * δ := by linarith
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      Complex.norm_natCast, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb0]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hp : (1 + (j : ℝ) * δ) ^ (ρ + 2).re ≤ (1 + (j : ℝ) * δ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hb (by simpa using (show ρ.re + 2 ≤ 3 by linarith))
    rw [Real.rpow_ofNat] at hp
    have hber : 1 + (j : ℝ) * δ ≤ (1 + δ) ^ j :=
      one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ δ) j
    calc (1 + (j : ℝ) * δ) ^ (ρ + 2).re ≤ (1 + (j : ℝ) * δ) ^ 3 := hp
      _ ≤ ((1 + δ) ^ j) ^ 3 := pow_le_pow_left₀ hb0.le hber 3
      _ = ((1 + δ) ^ 3) ^ j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  unfold numerator
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq ?_)
  set z := (1 + δ) ^ 3
  change (∑ j ∈ Finset.range 3, (Nat.choose 2 j : ℝ) * z ^ j) = (z + 1) ^ 2
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- The high-zero estimate with its exact quadratic-smoothing numerator bound. -/
theorem norm_upperKernel_le_high {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    ‖upperKernel δ ρ‖ ≤ R2 δ / (δ ^ 2 * ‖rising ρ 2‖) := by
  unfold upperKernel
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  exact div_le_div_of_nonneg_right (norm_numerator_le_R2 hδ.le hρ) (by positivity)



end TernaryGoldbach.RSBounds.QuadraticZeroKernel
end QuadraticZeroKernelDraft

/-! ## Preserved draft: `RSBounds/QuadraticKernelScaling.lean` -/
section QuadraticKernelScalingDraft

/-! Exact dilation identities for the twofold additive zero coefficient. -/

open Complex

namespace TernaryGoldbach.RSBounds.QuadraticKernelScaling

open PolynomialZeroKernel QuadraticZeroKernel

/-- The actual normalized second difference of a primitive zero term. -/
noncomputable def zeroCoefficient (x h : ℝ) (ρ : ℂ) : ℂ :=
  forwardDiff h 2 (antiderivative ρ 2) x / (h : ℂ) ^ 2

theorem antiderivative_two_mul {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (ρ : ℂ) :
    antiderivative ρ 2 (x * y) =
      (x : ℂ) ^ (ρ + 2) * antiderivative ρ 2 y := by
  simp only [antiderivative, Nat.cast_ofNat, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hx.le hy]
  ring

theorem forwardDiff_two_dilate (f : ℝ → ℂ) (x y δ : ℝ) :
    forwardDiff (δ * x) 2 f (x * y) =
      forwardDiff δ 2 (fun t => f (x * t)) y := by
  rw [forwardDiff_two, forwardDiff_two]
  rw [show x * y + 2 * (δ * x) = x * (y + 2 * δ) by ring,
    show x * y + δ * x = x * (y + δ) by ring]

/-- Dilation is exact before any zero-location estimate is used. -/
theorem zeroCoefficient_dilate {x y δ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hδ : 0 < δ) (ρ : ℂ) :
    zeroCoefficient (x * y) (δ * x) ρ =
      (x : ℂ) ^ ρ *
        (forwardDiff δ 2 (antiderivative ρ 2) y / (δ : ℂ) ^ 2) := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  rw [zeroCoefficient, forwardDiff_two_dilate, forwardDiff_two, forwardDiff_two]
  rw [antiderivative_two_mul hx (by linarith),
    antiderivative_two_mul hx (by linarith),
    antiderivative_two_mul hx hy.le]
  rw [Complex.cpow_add _ _ hxc, Complex.cpow_ofNat]
  push_cast
  field_simp [hxc, hδc]
  <;> ring

theorem zeroCoefficient_upper {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (ρ : ℂ) :
    zeroCoefficient x (δ * x) ρ = (x : ℂ) ^ ρ * QuadraticZeroKernel.upperKernel δ ρ := by
  simpa only [mul_one, QuadraticZeroKernel.upperKernel_eq_normalized_difference] using
    zeroCoefficient_dilate hx (by norm_num : (0 : ℝ) < 1) hδ ρ

theorem zeroCoefficient_lower {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ2 : 2 * δ < 1) (ρ : ℂ) :
    zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ =
      (x : ℂ) ^ ρ *
        (forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2) := by
  rw [show x - 2 * (δ * x) = x * (1 - 2 * δ) by ring]
  exact zeroCoefficient_dilate hx (by linarith) hδ ρ

theorem norm_zeroCoefficient_dilate {x y δ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hδ : 0 < δ) (ρ : ℂ) :
    ‖zeroCoefficient (x * y) (δ * x) ρ‖ =
      x ^ ρ.re * ‖forwardDiff δ 2 (antiderivative ρ 2) y / (δ : ℂ) ^ 2‖ := by
  rw [zeroCoefficient_dilate hx hy hδ, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]

end TernaryGoldbach.RSBounds.QuadraticKernelScaling
end QuadraticKernelScalingDraft

/-! ## Preserved draft: `RSBounds/QuadraticLowerKernel.lean` -/
section QuadraticLowerKernelDraft

/-! Lower-average bounds for the twofold additive smoothing coefficient.
The generic bounded-integral and finite-difference inequalities are reused.
-/

open Complex MeasureTheory Set
open TernaryGoldbach.RSBounds.PolynomialZeroKernel
open TernaryGoldbach.RSBounds.PolynomialZeroCancellation
open TernaryGoldbach.RSBounds.PolynomialLowerKernel
open TernaryGoldbach.RSBounds.QuadraticZeroKernel

namespace TernaryGoldbach.RSBounds.QuadraticLowerKernel

/-- The lower average has low-zero coefficient at most `1/|rho|`. -/
theorem norm_lower_difference_le_low {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2‖ ≤ 1 / ‖ρ‖ := by
  have hx : 0 < 1 - 2 * δ := by linarith
  rw [← zero_term_twofold_identity hρ hx hδ.le]
  have hm := norm_iteratedIntegral_le_const_on hδ.le
    (fun t : ℝ => (t : ℂ) ^ ρ / ρ) (1 / ‖ρ‖) 2 (1 - 2 * δ) (by
      intro t ht
      have ht0 : 0 < t := hx.trans_le ht.1
      have ht1 : t ≤ 1 := by norm_num at ht; linarith [ht.2]
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      exact div_le_div_of_nonneg_right (Real.rpow_le_one ht0.le ht1 hρ.le) (norm_nonneg _))
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  apply (div_le_iff₀ (pow_pos hδ 2)).mpr
  convert hm using 1 <;> ring

/-- The lower finite-difference numerator has coefficient sum `4`. -/
theorem norm_lower_difference_le_high {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2‖ ≤
      4 / (δ ^ 2 * ‖rising ρ 2‖) := by
  have hx : 0 < 1 - 2 * δ := by linarith
  have hm := norm_forwardDiff_le_const_on hδ.le (antiderivative ρ 2)
    (1 / ‖rising ρ 2‖) 2 (1 - 2 * δ) (by
      intro t ht
      have ht0 : 0 < t := hx.trans_le ht.1
      have ht1 : t ≤ 1 := by norm_num at ht; linarith [ht.2]
      rw [antiderivative, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      apply Real.rpow_le_one ht0.le ht1
      simpa using (show 0 ≤ ρ.re + 2 by linarith))
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ)‖ / δ ^ 2 ≤
      (2 ^ 2 * (1 / ‖rising ρ 2‖)) / δ ^ 2 := by gcongr
    _ = 4 / (δ ^ 2 * ‖rising ρ 2‖) := by ring

theorem four_le_R2 {δ : ℝ} (hδ : 0 ≤ δ) : 4 ≤ R2 δ := by
  have h1 : (1 : ℝ) ≤ (1 + δ) ^ 3 := one_le_pow₀ (by linarith)
  have h2 : (2 : ℝ) ^ 2 ≤ ((1 + δ) ^ 3 + 1) ^ 2 := by gcongr; linarith
  norm_num [R2] at h2 ⊢
  exact h2

/-- The same `R2` high-zero majorant can therefore be used for both signs. -/
theorem norm_lower_difference_le_high_common {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2‖ ≤
      R2 δ / (δ ^ 2 * ‖rising ρ 2‖) :=
  (norm_lower_difference_le_high hδ hδ2 hρ).trans
    (div_le_div_of_nonneg_right (four_le_R2 hδ.le) (by positivity))

/-- The upper low-zero factor `1+delta` also majorizes the lower average. -/
theorem norm_lower_difference_le_low_common {δ : ℝ} (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    ‖forwardDiff δ 2 (antiderivative ρ 2) (1 - 2 * δ) / (δ : ℂ) ^ 2‖ ≤
      (1 + δ) / ‖ρ‖ :=
  (norm_lower_difference_le_low hδ hδ2 hρ).trans
    (div_le_div_of_nonneg_right (by linarith) (norm_nonneg _))

end TernaryGoldbach.RSBounds.QuadraticLowerKernel
end QuadraticLowerKernelDraft

/-! ## Preserved draft: `RSBounds/QuadraticCoefficientBounds.lean` -/
section QuadraticCoefficientBoundsDraft

/-!
# Bounds for the actual twofold smoothing coefficients

The same near and far coefficients work for the upper and lower averages.
This module makes no zero-count or zero-free assumption; the real-part and
nonreal hypotheses on the argument are explicit.
-/

open Complex

namespace TernaryGoldbach.RSBounds.QuadraticCoefficientBounds

open PolynomialZeroKernel QuadraticZeroKernel QuadraticKernelScaling

theorem abs_im_pow_le_norm_rising_two (ρ : ℂ) :
    |ρ.im| ^ 3 ≤ ‖rising ρ 2‖ := by
  have hn (n : ℕ) : |ρ.im| ≤ ‖ρ + n‖ := by
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      Complex.abs_im_le_norm (ρ + n)
  have h0 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  norm_num [rising, norm_mul]
  calc
    |ρ.im| ^ 3 = |ρ.im| * |ρ.im| * |ρ.im| := by ring
    _ ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ := by
      gcongr
      · simpa using hn 1
      · simpa using hn 2

private theorem low_denominator_le {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (him : ρ.im ≠ 0) :
    (1 + δ) / ‖ρ‖ ≤ (1 + δ) / |ρ.im| :=
  div_le_div_of_nonneg_left (by linarith) (abs_pos.mpr him)
    (Complex.abs_im_le_norm ρ)

private theorem high_denominator_le {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (him : ρ.im ≠ 0) :
    R2 δ / (δ ^ 2 * ‖rising ρ 2‖) ≤ R2 δ / (δ ^ 2 * |ρ.im| ^ 3) := by
  apply div_le_div_of_nonneg_left (by unfold R2; positivity)
    (mul_pos (pow_pos hδ 2) (pow_pos (abs_pos.mpr him) 3))
  exact mul_le_mul_of_nonneg_left (abs_im_pow_le_norm_rising_two ρ) (by positivity)

/-- Near-zero bound for the actual upper average, with the factor `1+delta`. -/
theorem norm_zeroCoefficient_upper_le_low {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    {ρ : ℂ} (hr : 0 < ρ.re) (hr1 : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient x (δ * x) ρ‖ ≤ (1 + δ) * x ^ ρ.re / |ρ.im| := by
  rw [zeroCoefficient_upper hx hδ, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((QuadraticZeroKernel.norm_upperKernel_le_low hδ hr hr1).trans (low_denominator_le hδ him))
    (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

/-- The same near-zero bound for the lower average. -/
theorem norm_zeroCoefficient_lower_le_low {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ2 : 2 * δ < 1) {ρ : ℂ} (hr : 0 < ρ.re) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
      (1 + δ) * x ^ ρ.re / |ρ.im| := by
  rw [zeroCoefficient_lower hx hδ hδ2, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((QuadraticLowerKernel.norm_lower_difference_le_low_common hδ hδ2 hr).trans
      (low_denominator_le hδ him)) (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

/-- Far-zero bound for the actual upper average. -/
theorem norm_zeroCoefficient_upper_le_high {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    {ρ : ℂ} (hr : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient x (δ * x) ρ‖ ≤
      (R2 δ / δ ^ 2) * x ^ ρ.re / |ρ.im| ^ 3 := by
  rw [zeroCoefficient_upper hx hδ, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((QuadraticZeroKernel.norm_upperKernel_le_high hδ hr).trans (high_denominator_le hδ him))
    (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

/-- The same far-zero bound for the lower average. -/
theorem norm_zeroCoefficient_lower_le_high {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ2 : 2 * δ < 1) {ρ : ℂ} (hr : 0 ≤ ρ.re) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
      (R2 δ / δ ^ 2) * x ^ ρ.re / |ρ.im| ^ 3 := by
  rw [zeroCoefficient_lower hx hδ hδ2, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hh := mul_le_mul_of_nonneg_left
    ((QuadraticLowerKernel.norm_lower_difference_le_high_common hδ hδ2 hr).trans
      (high_denominator_le hδ him)) (Real.rpow_nonneg hx.le ρ.re)
  convert hh using 1 <;> ring

end TernaryGoldbach.RSBounds.QuadraticCoefficientBounds
end QuadraticCoefficientBoundsDraft

/-! ## Preserved draft: `RSBounds/QuadraticZetaFormula.lean` -/
section QuadraticZetaFormulaDraft

/-!
# A quadratic explicit formula with an explicit left remainder

The rational Mellin kernel is used off its half-plane of convergence. The
prime-sum identity uses only its equality with the Mellin integral on the
right line. The pole at zero contributes `log(2π)/2`.

The left vertical integral is retained, not identified with the trivial-zero
sum. This is a twofold integrated formula, not a numerical bound for psi.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.QuadraticZeta

open TernaryGoldbach.Explicit PolynomialExplicit QuadraticKernel QuadraticMellin
  QuadraticContourLimit QuadraticSubOne

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
    exact decayTwo_kernel.continuous_line _ (Or.inr rfl)
  have hi : Integrable (fun t : ℝ => mellin weight (((3 / 2 : ℝ) : ℂ) + t * I)) := by
    rw [hline]
    exact decayTwo_kernel.integrable_line (Or.inr rfl)
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

/-- The ordinary quadratic Mellin kernel gives a zero-sum formula with the
constant at zero evaluated and the left vertical remainder retained. -/
theorem explicit_formula_zeta_quadratic_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        (kernel u * (x : ℂ) ^ u)) atTop
        (𝓝 ((x : ℂ) / 6 - SsumG (1 : DirichletCharacter ℂ 1) weight x -
          (1 / (2 * π) : ℂ) *
            (∫ y : ℝ, contourIntegrand riemannZeta kernel x
              (((-1 / 2 : ℝ) : ℂ) + y * I)) - Complex.log (2 * π) / 2)) := by
  have hz0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have hlim := explicit_formula_zetaF_at_heights hx hT
  have hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ numerator s :=
    fun _ hs => differentiableAt_numerator hs
  have hM : DecayTwo (fun s => numerator s / s) 27 := by
    simpa only [← kernel_eq_numerator_div] using decayTwo_kernel
  have hmain := sub_one_contour_difference hH hM hx
  simp only [← kernel_eq_numerator_div, numerator_one, numerator_zero] at hmain
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
  have iR := QuadraticContourLimit.integrable_contour_right ldatum_zeta2 decayTwo_kernel hx
  have iL := integrable_zetaF_contour_left decayTwo_kernel hx
  have iR1 := QuadraticContourLimit.integrable_contour_right ldatum_sub_one decayTwo_kernel hx
  have iL1 := integrable_sub_one_contour_left decayTwo_kernel hx
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
  have hmain' : (x : ℂ) / 6 = (1 / (2 * π) : ℂ) * (A1 - B1v) -
      logDeriv (fun s : ℂ => s - 1) 0 / 2 := by
    calc
      _ = (1 / 6 : ℂ) * (x : ℂ) := by ring
      _ = (1 / (2 * π) : ℂ) * (A1 - B1v) -
          logDeriv (fun s : ℂ => s - 1) 0 * (1 / 2) := hmain
      _ = _ := by ring
  convert hlim using 2
  rw [hmain', hS, IL, hzero]
  ring

/-- Existential form of the quadratic formula for zeta. -/
theorem explicit_formula_zeta_quadratic {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        (kernel u * (x : ℂ) ^ u)) atTop
        (𝓝 ((x : ℂ) / 6 - SsumG (1 : DirichletCharacter ℂ 1) weight x -
          (1 / (2 * π) : ℂ) *
            (∫ y : ℝ, contourIntegrand riemannZeta kernel x
              (((-1 / 2 : ℝ) : ℂ) + y * I)) - Complex.log (2 * π) / 2)) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  exact ⟨T, hT.mem, explicit_formula_zeta_quadratic_at_heights hT hx⟩

/-- The unevaluated left vertical contribution to the second primitive. -/
noncomputable def psi2LeftRemainder (x : ℝ) : ℂ :=
  (x : ℂ) ^ 2 / (2 * π) *
    ∫ y : ℝ, contourIntegrand riemannZeta kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)

/-- The fixed-strip explicit formula written for the actual twofold
primitive `Psi2 x = ∑ Λ(n) (x-n)_+^2/2`. -/
theorem explicit_formula_Psi2_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        ((x : ℂ) ^ (u + 2) / (u * (u + 1) * (u + 2)))) atTop
        (𝓝 ((x : ℂ) ^ 3 / 6 - (QuadraticPsi.Psi2 x : ℂ) - psi2LeftRemainder x -
          (x : ℂ) ^ 2 * Complex.log (2 * π) / 2)) := by
  have hlim := explicit_formula_zeta_quadratic_at_heights hT hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsum (k : ℕ) :
      (x : ℂ) ^ 2 * (∑ u ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) u : ℂ) * (kernel u * (x : ℂ) ^ u)) =
      ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        ((x : ℂ) ^ (u + 2) / (u * (u + 1) * (u + 2))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Complex.cpow_add _ _ hx0, Complex.cpow_ofNat]
    unfold kernel
    ring
  have hscaled := hlim.const_mul ((x : ℂ) ^ 2)
  simp_rw [hsum] at hscaled
  simp only [mul_sub] at hscaled
  rw [QuadraticPsiMellin.pow_two_mul_SsumG_quadratic_eq_Psi2 hx] at hscaled
  convert hscaled using 2 <;> unfold psi2LeftRemainder <;> ring

/-- Existential form of the twofold primitive formula. -/
theorem explicit_formula_Psi2 {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        ((x : ℂ) ^ (u + 2) / (u * (u + 1) * (u + 2)))) atTop
        (𝓝 ((x : ℂ) ^ 3 / 6 - (QuadraticPsi.Psi2 x : ℂ) - psi2LeftRemainder x -
          (x : ℂ) ^ 2 * Complex.log (2 * π) / 2)) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  exact ⟨T, hT.mem, explicit_formula_Psi2_at_heights hT hx⟩

end TernaryGoldbach.RSBounds.QuadraticZeta
end QuadraticZetaFormulaDraft

/-! ## Preserved draft: `RSBounds/QuadraticAveragedFormula.lean` -/
section QuadraticAveragedFormulaDraft
/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/

/-!
# Assembling the twofold averaged explicit formula

All three primitive formulas use one sequence of good contour heights. Their
second finite difference gives the upper polynomial smoothing of psi, with
main term `x + h`, constant `-log(2*pi)`, and an explicit left remainder.
No estimate for the zero sum or remainder is assumed or asserted here.
-/

open Complex Finset Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.QuadraticAveraged

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialZeroKernel
open QuadraticZeta QuadraticPsi QuadraticZeroKernel QuadraticKernelScaling

/-- The left contour remainder after the same averaging operation. -/
noncomputable def leftRemainder (x h : ℝ) : ℂ :=
  forwardDiff h 2 psi2LeftRemainder x / (h : ℂ) ^ 2

private theorem antiderivative_two_eq (ρ : ℂ) (x : ℝ) :
    antiderivative ρ 2 x =
      (x : ℂ) ^ (ρ + 2) / (ρ * (ρ + 1) * (ρ + 2)) := by
  norm_num [antiderivative, rising]

private theorem forwardDiff_two_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 2 (fun t => ∑ i ∈ s, f i t) x =
      ∑ i ∈ s, forwardDiff h 2 (f i) x := by
  simp only [forwardDiff_two, sum_add_distrib, sum_sub_distrib, mul_sum]

private theorem forwardDiff_two_mul (c : ℂ) (f : ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 2 (fun t => c * f t) x = c * forwardDiff h 2 f x := by
  simp only [forwardDiff_two]
  ring

private theorem forwardDiff_two_sub (f g : ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 2 (fun t => f t - g t) x =
      forwardDiff h 2 f x - forwardDiff h 2 g x := by
  simp only [forwardDiff_two]
  ring

/-- The finite difference of the integrated main term. -/
theorem normalized_main_term {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    forwardDiff h 2 (fun t : ℝ => (t : ℂ) ^ 3 / 6) x / (h : ℂ) ^ 2 =
      ((x + h : ℝ) : ℂ) := by
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  rw [forwardDiff_two]
  push_cast
  field_simp [hh0]
  ring

/-- Twofold averaging leaves the constant at the zero pole unchanged. -/
theorem normalized_zero_pole {h : ℝ} (hh : h ≠ 0) (x : ℝ) (c : ℂ) :
    forwardDiff h 2 (fun t : ℝ => (t : ℂ) ^ 2 * c / 2) x / (h : ℂ) ^ 2 = c := by
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  rw [forwardDiff_two]
  push_cast
  field_simp [hh0]
  ring

/-- Casting the finite arithmetic smoothing identity into the complex formula. -/
theorem normalized_Psi2 {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    forwardDiff h 2 (fun t => (Psi2 t : ℂ)) x / (h : ℂ) ^ 2 =
      (psiUpper N x h : ℂ) := by
  have hc := congrArg (fun t : ℝ => (t : ℂ))
    (secondDifference_Psi2 hx hh hN)
  simpa only [forwardDiff_two, secondDifference, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat] using hc

private theorem tendsto_normalized_forwardDiff_two
    {F : ℕ → ℝ → ℂ} {G : ℝ → ℂ} (x h : ℝ)
    (h0 : Tendsto (fun k => F k x) atTop (𝓝 (G x)))
    (h1 : Tendsto (fun k => F k (x + h)) atTop (𝓝 (G (x + h))))
    (h2 : Tendsto (fun k => F k (x + 2 * h)) atTop (𝓝 (G (x + 2 * h)))) :
    Tendsto (fun k => forwardDiff h 2 (F k) x / (h : ℂ) ^ 2) atTop
      (𝓝 (forwardDiff h 2 G x / (h : ℂ) ^ 2)) := by
  simpa only [forwardDiff_two] using
    ((h2.sub (h1.const_mul 2)).add h0).div_const ((h : ℂ) ^ 2)

/-- The upper twofold averaged explicit formula along a common sequence
of good heights. The left contour remainder is retained explicitly. -/
theorem explicit_formula_upper_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ) atTop
      (𝓝 (((x + h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
        leftRemainder x h - Complex.log (2 * Real.pi))) := by
  let F : ℕ → ℝ → ℂ := fun k t => ∑ ρ ∈ zerosRectD zetaF (T k),
    (multRectD zetaF (T k) ρ : ℂ) * antiderivative ρ 2 t
  let G : ℝ → ℂ := fun t => (t : ℂ) ^ 3 / 6 - (Psi2 t : ℂ) -
    psi2LeftRemainder t - (t : ℂ) ^ 2 * Complex.log (2 * Real.pi) / 2
  have hlim (t : ℝ) (ht : 0 < t) : Tendsto (fun k => F k t) atTop (𝓝 (G t)) := by
    simpa only [F, G, antiderivative_two_eq] using
      explicit_formula_Psi2_at_heights hT ht
  have havg := tendsto_normalized_forwardDiff_two x h (hlim x hx)
    (hlim (x + h) (by linarith)) (hlim (x + 2 * h) (by linarith))
  have hsum (k : ℕ) : forwardDiff h 2 (F k) x / (h : ℂ) ^ 2 =
      ∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ := by
    dsimp only [F]
    rw [forwardDiff_two_sum, sum_div]
    apply sum_congr rfl
    intro ρ _
    rw [forwardDiff_two_mul, mul_div_assoc]
    rfl
  have hvalue : forwardDiff h 2 G x / (h : ℂ) ^ 2 =
      ((x + h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
        leftRemainder x h - Complex.log (2 * Real.pi) := by
    dsimp only [G]
    rw [forwardDiff_two_sub, forwardDiff_two_sub, forwardDiff_two_sub,
      sub_div, sub_div, sub_div, normalized_main_term hh.ne',
      normalized_Psi2 hx.le hh hN, normalized_zero_pole hh.ne']
    rfl
  simpa only [hsum, hvalue] using havg

/-- Existence form of the upper averaged formula; no zero-location premise. -/
theorem explicit_formula_upper {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ) atTop
        (𝓝 (((x + h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
          leftRemainder x h - Complex.log (2 * Real.pi))) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  exact ⟨T, hT.mem, explicit_formula_upper_at_heights hT hx hh hN⟩

/-- The same formula shifted to give the lower polynomial smoothing. -/
theorem explicit_formula_lower_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x h : ℝ} (hx : 2 * h < x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient (x - 2 * h) h ρ) atTop
      (𝓝 (((x - h : ℝ) : ℂ) - (psiLower N x h : ℂ) -
        leftRemainder (x - 2 * h) h - Complex.log (2 * Real.pi))) := by
  have hv := explicit_formula_upper_at_heights hT (x := x - 2 * h)
    (by linarith) hh (show x - 2 * h + 2 * h ≤ N by linarith)
  simpa only [psiUpper, psiLower, sub_add_cancel,
    show x - 2 * h + h = x - h by ring] using hv

end TernaryGoldbach.RSBounds.QuadraticAveraged
end QuadraticAveragedFormulaDraft
