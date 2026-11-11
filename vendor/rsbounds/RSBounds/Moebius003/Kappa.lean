/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Defs
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# `∑ μ(d)/d² = 6/π² = κ`, and numerical bounds for `κ`
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius

theorem hasSum_moebius_div_sq : HasSum (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2) κ := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h1 := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h1
  have hL : LSeries (fun n => (μ n : ℂ)) 2 = 6 / (π : ℂ) ^ 2 := by
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp at h1 ⊢
    linear_combination h1
  have hsum := (LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  rw [hL] at hsum
  have hterm : LSeries.term (fun n => (μ n : ℂ)) 2 =
      fun d : ℕ => (((μ d : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn]
      push_cast
      congr 1
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  unfold LSeriesHasSum at hsum
  rw [hterm] at hsum
  have : ((κ : ℝ) : ℂ) = 6 / (π : ℂ) ^ 2 := by rw [κ]; push_cast; rfl
  rw [← this] at hsum
  exact Complex.hasSum_ofReal.mp hsum

theorem summable_moebius_div_sq : Summable (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ 2) :=
  hasSum_moebius_div_sq.summable

/-- `κ ∈ [0.6079267, 0.6079274]`. -/
theorem κ_lo : (0.6079267 : ℝ) ≤ κ := by
  rw [κ, le_div_iff₀ (by positivity)]
  have := Real.pi_lt_d6
  nlinarith [Real.pi_pos, mul_pos (sub_pos.2 this) (by linarith [Real.pi_pos] : 0 < 3.141593 + π)]

theorem κ_hi : κ ≤ (0.6079274 : ℝ) := by
  rw [κ, div_le_iff₀ (by positivity)]
  have := Real.pi_gt_d6
  nlinarith [Real.pi_pos, mul_pos (sub_pos.2 this) (by linarith [Real.pi_pos] : 0 < 3.141592 + π)]

theorem κ_pos : 0 < κ := lt_of_lt_of_le (by norm_num) κ_lo

end TernaryGoldbach.RSBounds.Moebius003
