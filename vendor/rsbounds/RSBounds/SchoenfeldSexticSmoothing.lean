import Mathlib

/-!
# The exact sextic kernel for sixfold additive smoothing

The order-6 analogue of `PolynomialSmoothing`. `W` is the distribution function of a sum of six
variables uniformly distributed on `[0,1]` (the Irwin–Hall distribution), written as a finite
difference of the truncated sixth power. The proofs are polynomial identities and inequalities.

The bounds `0 ≤ W ≤ 1` are proved on `[0,3]` from the Bernstein form of each polynomial piece,
whose coefficients are all nonnegative, and extended to `[3,6]` by the reflection
`W t + W (6 - t) = 1`.
-/

namespace TernaryGoldbach.RSBounds.SchoenfeldSexticSmoothing

/-- The normalized sixth difference of the truncated sixth power. -/
noncomputable def W (t : ℝ) : ℝ :=
  ((max t 0) ^ 6 - 6 * (max (t - 1) 0) ^ 6 + 15 * (max (t - 2) 0) ^ 6 -
    20 * (max (t - 3) 0) ^ 6 + 15 * (max (t - 4) 0) ^ 6 - 6 * (max (t - 5) 0) ^ 6 +
    (max (t - 6) 0) ^ 6) / 720

private theorem posPart_pow_six_add (t : ℝ) :
    (max t 0) ^ 6 + (max (-t) 0) ^ 6 = t ^ 6 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_right (by linarith : -t ≤ 0)]
    ring
  · rw [max_eq_right ht.le, max_eq_left (by linarith : 0 ≤ -t)]
    ring

/-- Reflection about the midpoint of the sixfold averaging interval. -/
theorem W_add_reflect (t : ℝ) : W t + W (6 - t) = 1 := by
  have h0 := posPart_pow_six_add t
  have h1 := posPart_pow_six_add (t - 1)
  have h2 := posPart_pow_six_add (t - 2)
  have h3 := posPart_pow_six_add (t - 3)
  have h4 := posPart_pow_six_add (t - 4)
  have h5 := posPart_pow_six_add (t - 5)
  have h6 := posPart_pow_six_add (t - 6)
  unfold W
  rw [show 6 - t - 1 = -(t - 5) by ring,
    show 6 - t - 2 = -(t - 4) by ring,
    show 6 - t - 3 = -(t - 3) by ring,
    show 6 - t - 4 = -(t - 2) by ring,
    show 6 - t - 5 = -(t - 1) by ring,
    show 6 - t - 6 = -t by ring,
    show 6 - t = -(t - 6) by ring]
  linear_combination (h0 - 6 * h1 + 15 * h2 - 20 * h3 + 15 * h4 - 6 * h5 + h6) / 720

theorem W_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : W t = 0 := by
  unfold W
  rw [max_eq_right ht,
    max_eq_right (by linarith : t - 1 ≤ 0),
    max_eq_right (by linarith : t - 2 ≤ 0),
    max_eq_right (by linarith : t - 3 ≤ 0),
    max_eq_right (by linarith : t - 4 ≤ 0),
    max_eq_right (by linarith : t - 5 ≤ 0),
    max_eq_right (by linarith : t - 6 ≤ 0)]
  norm_num

theorem W_eq_one_of_six_le {t : ℝ} (ht : 6 ≤ t) : W t = 1 := by
  have h := W_add_reflect t
  rw [W_eq_zero_of_nonpos (by linarith : 6 - t ≤ 0), add_zero] at h
  exact h

/-- A sum of nonnegative multiples of `s^i u^(6-i)` is nonnegative for `s, u ≥ 0`. -/
private theorem bernstein_nonneg {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    {c0 c1 c2 c3 c4 c5 c6 : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3)
    (h4 : 0 ≤ c4) (h5 : 0 ≤ c5) (h6 : 0 ≤ c6) :
    0 ≤ c0 * u ^ 6 + c1 * s * u ^ 5 + c2 * s ^ 2 * u ^ 4 + c3 * s ^ 3 * u ^ 3 +
      c4 * s ^ 4 * u ^ 2 + c5 * s ^ 5 * u + c6 * s ^ 6 := by
  positivity

private theorem W_bounds_of_le_three {t : ℝ} (ht : t ≤ 3) :
    0 ≤ W t ∧ W t ≤ 1 := by
  rcases le_or_gt t 0 with ht0 | ht0
  · rw [W_eq_zero_of_nonpos ht0]
    norm_num
  rcases le_or_gt t 1 with ht1 | ht1
  · -- `t ∈ [0,1]`: `W t = t^6/720`
    have he : W t = t ^ 6 / 720 := by
      unfold W
      rw [max_eq_left ht0.le,
        max_eq_right (by linarith : t - 1 ≤ 0),
        max_eq_right (by linarith : t - 2 ≤ 0),
        max_eq_right (by linarith : t - 3 ≤ 0),
        max_eq_right (by linarith : t - 4 ≤ 0),
        max_eq_right (by linarith : t - 5 ≤ 0),
        max_eq_right (by linarith : t - 6 ≤ 0)]
      ring
    have hp := pow_le_pow_left₀ ht0.le ht1 6
    rw [he]
    constructor
    · positivity
    · norm_num at hp
      linarith
  rcases le_or_gt t 2 with ht2 | ht2
  · -- `t ∈ [1,2]`, Bernstein form in `s = t - 1`, `u = 2 - t`
    have hs : 0 ≤ t - 1 := by linarith
    have hu : 0 ≤ 2 - t := by linarith
    have he : W t = 1 / 720 * (2 - t) ^ 6 + 6 * (1 / 360) * (t - 1) * (2 - t) ^ 5 +
        15 * (1 / 180) * (t - 1) ^ 2 * (2 - t) ^ 4 + 20 * (1 / 90) * (t - 1) ^ 3 * (2 - t) ^ 3 +
        15 * (1 / 45) * (t - 1) ^ 4 * (2 - t) ^ 2 + 6 * (2 / 45) * (t - 1) ^ 5 * (2 - t) +
        29 / 360 * (t - 1) ^ 6 := by
      unfold W
      rw [max_eq_left ht0.le,
        max_eq_left (by linarith : 0 ≤ t - 1),
        max_eq_right (by linarith : t - 2 ≤ 0),
        max_eq_right (by linarith : t - 3 ≤ 0),
        max_eq_right (by linarith : t - 4 ≤ 0),
        max_eq_right (by linarith : t - 5 ≤ 0),
        max_eq_right (by linarith : t - 6 ≤ 0)]
      ring
    have he' : 1 - W t = 719 / 720 * (2 - t) ^ 6 + 6 * (359 / 360) * (t - 1) * (2 - t) ^ 5 +
        15 * (179 / 180) * (t - 1) ^ 2 * (2 - t) ^ 4 +
        20 * (89 / 90) * (t - 1) ^ 3 * (2 - t) ^ 3 +
        15 * (44 / 45) * (t - 1) ^ 4 * (2 - t) ^ 2 + 6 * (43 / 45) * (t - 1) ^ 5 * (2 - t) +
        331 / 360 * (t - 1) ^ 6 := by
      rw [he]; ring
    constructor
    · rw [he]
      exact bernstein_nonneg hs hu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · have := bernstein_nonneg hs hu (c0 := 719 / 720) (c1 := 6 * (359 / 360))
        (c2 := 15 * (179 / 180)) (c3 := 20 * (89 / 90)) (c4 := 15 * (44 / 45))
        (c5 := 6 * (43 / 45)) (c6 := 331 / 360) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      linarith
  · -- `t ∈ [2,3]`, Bernstein form in `s = t - 2`, `u = 3 - t`
    have hs : 0 ≤ t - 2 := by linarith
    have hu : 0 ≤ 3 - t := by linarith
    have he : W t = 29 / 360 * (3 - t) ^ 6 + 6 * (7 / 60) * (t - 2) * (3 - t) ^ 5 +
        15 * (1 / 6) * (t - 2) ^ 2 * (3 - t) ^ 4 + 20 * (7 / 30) * (t - 2) ^ 3 * (3 - t) ^ 3 +
        15 * (19 / 60) * (t - 2) ^ 4 * (3 - t) ^ 2 + 6 * (49 / 120) * (t - 2) ^ 5 * (3 - t) +
        1 / 2 * (t - 2) ^ 6 := by
      unfold W
      rw [max_eq_left ht0.le,
        max_eq_left (by linarith : 0 ≤ t - 1),
        max_eq_left (by linarith : 0 ≤ t - 2),
        max_eq_right (by linarith : t - 3 ≤ 0),
        max_eq_right (by linarith : t - 4 ≤ 0),
        max_eq_right (by linarith : t - 5 ≤ 0),
        max_eq_right (by linarith : t - 6 ≤ 0)]
      ring
    have he' : 1 - W t = 331 / 360 * (3 - t) ^ 6 + 6 * (53 / 60) * (t - 2) * (3 - t) ^ 5 +
        15 * (5 / 6) * (t - 2) ^ 2 * (3 - t) ^ 4 + 20 * (23 / 30) * (t - 2) ^ 3 * (3 - t) ^ 3 +
        15 * (41 / 60) * (t - 2) ^ 4 * (3 - t) ^ 2 + 6 * (71 / 120) * (t - 2) ^ 5 * (3 - t) +
        1 / 2 * (t - 2) ^ 6 := by
      rw [he]; ring
    constructor
    · rw [he]
      exact bernstein_nonneg hs hu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · have := bernstein_nonneg hs hu (c0 := 331 / 360) (c1 := 6 * (53 / 60))
        (c2 := 15 * (5 / 6)) (c3 := 20 * (23 / 30)) (c4 := 15 * (41 / 60))
        (c5 := 6 * (71 / 120)) (c6 := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      linarith

theorem W_bounds (t : ℝ) : 0 ≤ W t ∧ W t ≤ 1 := by
  rcases le_or_gt t 3 with ht | ht
  · exact W_bounds_of_le_three ht
  · have h := W_bounds_of_le_three (show 6 - t ≤ 3 by linarith)
    have he := W_add_reflect t
    constructor <;> linarith

theorem W_nonneg (t : ℝ) : 0 ≤ W t := (W_bounds t).1

theorem W_le_one (t : ℝ) : W t ≤ 1 := (W_bounds t).2

theorem continuous_W : Continuous W := by
  unfold W
  fun_prop

/-- Sixfold finite differences of the integrated main term `x^7/5040`.
After dividing by `h^6`, the upper average differs from `x` by exactly `3h`. -/
theorem sixth_difference_main_term {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    ((x + 6 * h) ^ 7 - 6 * (x + 5 * h) ^ 7 + 15 * (x + 4 * h) ^ 7 - 20 * (x + 3 * h) ^ 7 +
      15 * (x + 2 * h) ^ 7 - 6 * (x + h) ^ 7 + x ^ 7) / (5040 * h ^ 6) = x + 3 * h := by
  field_simp
  ring

/-- The corresponding lower average has main term `x - 3h`. -/
theorem sixth_difference_main_term_lower {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    (x ^ 7 - 6 * (x - h) ^ 7 + 15 * (x - 2 * h) ^ 7 - 20 * (x - 3 * h) ^ 7 +
      15 * (x - 4 * h) ^ 7 - 6 * (x - 5 * h) ^ 7 + (x - 6 * h) ^ 7) / (5040 * h ^ 6) =
        x - 3 * h := by
  field_simp
  ring

end TernaryGoldbach.RSBounds.SchoenfeldSexticSmoothing
