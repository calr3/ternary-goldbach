import TernaryGoldbach.MinorArcs.Eta2DDTaylor

/-!
# [H, Lemma B.1.2, (B.6)] with constant `32`: `‖(2πt)² η̂₂(t)‖ ≤ 32` for all `t ≥ 0`

[H] proves `|η̂₂''|_∞ ≤ 31.521` with an interval-arithmetic computation for `|t| < 655`. We prove the
slightly weaker constant `32` without that computation:
* `t ≥ 2` (`norm_eta2DD_ge_two`): the expansion `eta2DD t = F(e(−t/4), 1/(2πt)) + O*(6120/(2πt)³)`
  and a kernel-checked bound `‖F(z, w)‖ + 6120w³ ≤ 32` for `‖z‖ = 1`, `0 ≤ w ≤ 2/25`
  (`Eta2DDExpand.lean`);
* `0 ≤ t ≤ 2` (`norm_eta2DD_le_two`): Taylor polynomials of degree `< 50` in `x = 2πt` and a
  kernel-checked bisection of `[0, 12.6]` (`Eta2DDTaylor.lean`).

The true maximum is `31.52065` at `t ≈ 17.415`; the margin in the second region is about `0.47`.
-/

open Real Complex

namespace TernaryGoldbach.MinorArcs

theorem gridB_pos : chk 12 1 (-1) 1 0 (2 / 25) = true := by decide +kernel

theorem gridB_neg : chk 20 (-1) (-1) 1 0 (2 / 25) = true := by decide +kernel

theorem gridC : chkC 10 0 Xc = true := by decide +kernel

/-- **`‖eta2DD t‖ ≤ 32` for `t ≥ 2`.** -/
theorem norm_eta2DD_ge_two {t : ℝ} (ht : 2 ≤ t) : ‖eta2DD t‖ ≤ 32 := by
  have ht0 : 0 < t := by linarith
  set w : ℝ := 1 / (2 * π * t) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 2 / 25 := by
    rw [hw, div_le_iff₀ (by positivity)]
    have := Real.pi_gt_d2
    nlinarith [mul_nonneg (sub_nonneg.2 this.le) (sub_nonneg.2 ht)]
  have hR := norm_eta2DD_sub_Fz ht0.ne'
  rw [← hw, abs_of_nonneg hw0] at hR
  obtain ⟨s, hs, m, hm, hz⟩ := exists_zm (norm_e (-(1 / 4 * t)))
  have hF : ‖Fz (e (-(1 / 4 * t))) w‖ + 6120 * w ^ 3 ≤ 32 := by
    rw [hz]
    rcases hs with rfl | rfl
    · have := chk_sound (s := 1) (Or.inl rfl) 12 (-1) 1 0 (2 / 25) le_rfl gridB_pos m w
        (by push_cast; exact hm.1) (by push_cast; exact hm.2) (by push_cast; exact hw0)
        (by push_cast; exact hw1)
      simpa using this
    · have := chk_sound (s := -1) (Or.inr rfl) 20 (-1) 1 0 (2 / 25) le_rfl gridB_neg m w
        (by push_cast; exact hm.1) (by push_cast; exact hm.2) (by push_cast; exact hw0)
        (by push_cast; exact hw1)
      simpa using this
  have := norm_sub_norm_le (eta2DD t) (Fz (e (-(1 / 4 * t))) w)
  linarith

/-- **`‖eta2DD t‖ ≤ 32` for `0 ≤ t ≤ 2`.** -/
theorem norm_eta2DD_le_two {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2) : ‖eta2DD t‖ ≤ 32 := by
  have h := chkC_sound 10 0 Xc le_rfl le_rfl gridC (2 * π * t) (by push_cast; positivity) (by
    simp only [Xc]; push_cast
    have := Real.pi_lt_d2
    nlinarith)
  have hπ : (2 * π * t) / (2 * π) = t := by field_simp
  rwa [hπ] at h

/-- **[H, (B.6)] with `32`**: `‖eta2DD t‖ ≤ 32` for all `t ≥ 0`. -/
theorem norm_eta2DD_le {t : ℝ} (ht : 0 ≤ t) : ‖eta2DD t‖ ≤ 32 := by
  rcases le_total t 2 with h | h
  · exact norm_eta2DD_le_two ht h
  · exact norm_eta2DD_ge_two h

end TernaryGoldbach.MinorArcs
