import TernaryGoldbach.Explicit.LGrowthPoly
import TernaryGoldbach.Explicit.ExplicitFormula

/-!
# Zero counts with polynomial growth, and sums over zeros

`B'_T = 1400 q⁹ (q+1)(|T|+22)(1.25(|T|+11))^{10}` bounds `|L|` on `|z − (2 + iT)| ≤ 10`
(`LGrowthPoly` for `ℜz ≤ 1/4`, `LGrowth` otherwise), so Jensen gives `O(log qT)` zeros per window.
-/

open Complex MeasureTheory Set Filter
open scoped Real

namespace TernaryGoldbach.Explicit

/-- `B'_T`. -/
noncomputable def BP (N : ℕ) (T : ℝ) : ℝ :=
  1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) * (1.25 * (|T| + 11)) ^ (10 : ℝ)

theorem one_le_BP {N : ℕ} [NeZero N] (T : ℝ) : 1400 ≤ BP N T := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h9 : (1:ℝ) ≤ (N : ℝ) ^ 9 := one_le_pow₀ hN1
  have hp : (1:ℝ) ≤ (1.25 * (|T| + 11)) ^ (10 : ℝ) :=
    Real.one_le_rpow (by nlinarith [abs_nonneg T]) (by norm_num)
  unfold BP
  have h1 : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by nlinarith
  have h2 : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) := by nlinarith [abs_nonneg T]
  have h3 : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) * (1.25 * (|T| + 11)) ^ (10 : ℝ) := by
    nlinarith
  nlinarith

theorem norm_L_le_BP {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T : ℝ} {w : ℂ} (hw : w ∈ Metric.closedBall (2 + T * I) 10) :
    ‖χ.LFunction w‖ ≤ BP N T := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have hre := Complex.abs_re_le_norm (w - (2 + T * I))
  have him := Complex.abs_im_le_norm (w - (2 + T * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im,
    Complex.add_im, Complex.im_ofNat, Complex.mul_im, zero_add, add_zero] at hre him
  have hwim1 : |w.im| ≤ |T| + 10 := by
    have := abs_sub_abs_le_abs_sub w.im T; linarith [abs_sub_comm w.im T]
  have hre1 : -8 ≤ w.re := by linarith [neg_abs_le (w.re - 2)]
  have hre2 : w.re ≤ 12 := by linarith [le_abs_self (w.re - 2)]
  rcases le_total w.re (1 / 4) with h | h
  · refine (norm_LFunction_left_poly hχ hχ1 hre1 h).trans ?_
    unfold BP
    have h1 : |w.im| + 9 ≤ |T| + 22 := by linarith
    have h2 : (1.25 * (|w.im| + 1)) ^ (10 : ℝ) ≤ (1.25 * (|T| + 11)) ^ (10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hA : 0 ≤ 1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) h2 (by positivity) (by positivity)
  · refine (norm_LFunction_le hχ1 (by linarith)).trans ?_
    have hwn : ‖w‖ ≤ |T| + 22 := by
      refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
      rw [abs_of_pos (by linarith : (0:ℝ) < w.re)]; linarith
    have h4 : ((N : ℝ) + 1) * ‖w‖ / w.re ≤ 4 * ((N : ℝ) + 1) * (|T| + 22) := by
      rw [div_le_iff₀ (by linarith)]
      have hp : 0 ≤ 4 * ((N : ℝ) + 1) * (|T| + 22) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hwn (by positivity : (0:ℝ) ≤ (N : ℝ) + 1)
      have h2 := mul_le_mul_of_nonneg_left h hp
      nlinarith
    refine h4.trans ?_
    have h9 : (1:ℝ) ≤ (N : ℝ) ^ 9 := one_le_pow₀ hN1
    have hp : (1:ℝ) ≤ (1.25 * (|T| + 11)) ^ (10 : ℝ) :=
      Real.one_le_rpow (by nlinarith [abs_nonneg T]) (by norm_num)
    unfold BP
    have hq : 0 ≤ ((N : ℝ) + 1) * (|T| + 22) := by positivity
    calc 4 * ((N : ℝ) + 1) * (|T| + 22) = 4 * (((N : ℝ) + 1) * (|T| + 22)) := by ring
      _ ≤ 1400 * (N : ℝ) ^ 9 * (1.25 * (|T| + 11)) ^ (10 : ℝ) * (((N : ℝ) + 1) * (|T| + 22)) := by
        have : (4:ℝ) ≤ 1400 * (N : ℝ) ^ 9 * (1.25 * (|T| + 11)) ^ (10 : ℝ) := by nlinarith
        nlinarith
      _ = _ := by ring

/-- **Jensen with polynomial growth**: at most `log(B'_T/0.355)/log(10/r)` zeros in `|ρ − (2+iT)| ≤ r`. -/
theorem zero_count_poly {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (T : ℝ) {r : ℝ} (hr : 0 < r) (hr10 : r < 10) :
    ((∑ᶠ u, MeromorphicOn.divisor χ.LFunction (Metric.closedBall (2 + T * I) |r|) u : ℤ) : ℝ) ≤
      Real.log (BP N T / 0.355) / Real.log (10 / r) := by
  have hc := norm_L_center_ge χ T
  have hc0 : χ.LFunction (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := one_le_BP (N := N) T
  have hf : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall (2 + T * I) |(10 : ℝ)|) := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt z
  have h := hf.sum_divisor_le (r := r) (R := 10) (by rw [abs_of_pos hr]; exact hr)
    (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0:ℝ) < 10)]; exact hr10) (by linarith) hc0
    (fun w hw => norm_L_le_BP hχ hχ1 (Metric.sphere_subset_closedBall (by
      rwa [abs_of_pos (by norm_num : (0:ℝ) < 10)] at hw)))
  refine h.trans ?_
  have hpos : 0 < BP N T / ‖χ.LFunction (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (BP N T / ‖χ.LFunction (2 + T * I)‖) ≤ Real.log (BP N T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  exact div_le_div_of_nonneg_right hle (Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith))

end TernaryGoldbach.Explicit
