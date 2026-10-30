import TernaryGoldbach.Helfgott.Defs

/-!
# The final numerical inequality of [H, §7.4]

Proved, with no `sorry`.
-/

namespace TernaryGoldbach.Helfgott

theorem xOf_denom_bounds : 0 < 2 + 9 / (196 * √(2 * Real.pi)) ∧
    2 + 9 / (196 * √(2 * Real.pi)) ≤ 2.02 := by
  have hpi := Real.pi_gt_three
  have hs : (2.4 : ℝ) ≤ √(2 * Real.pi) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < √(2 * Real.pi) := by linarith
  refine ⟨by positivity, ?_⟩
  have : 9 / (196 * √(2 * Real.pi)) ≤ 9 / (196 * 2.4) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2 : (9 : ℝ) / (196 * 2.4) ≤ 0.02 := by norm_num
  linarith

/-- The final numerical step of [H, §7.4]: for `N ≥ 10²⁷`,
`7.3306 N^{3/2} log N < (1.058259 - 1.00948) x²/κ`. -/
theorem final_inequality (N : ℕ) (hN : 10 ^ 27 ≤ N) :
    7.3306 * (N * √N) * Real.log N < (1.058259 - 1.00948) * xOf N ^ 2 / κ := by
  obtain ⟨hc0, hc1⟩ := xOf_denom_bounds
  set c := 2 + 9 / (196 * √(2 * Real.pi)) with hc
  have hNr : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNr
  set s := √(√(N : ℝ)) with hs
  have hs2 : s ^ 2 = √(N : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = (N : ℝ) := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, Real.sq_sqrt hN0.le]
  have hs0 : 0 < s := Real.sqrt_pos.2 (Real.sqrt_pos.2 hN0)
  have hsbig : (10 : ℝ) ^ 6 ≤ s := by
    by_contra h
    push Not at h
    have : s ^ 4 < ((10 : ℝ) ^ 6) ^ 4 := pow_lt_pow_left₀ h hs0.le (by norm_num)
    rw [hs4] at this
    linarith [show ((10 : ℝ) ^ 6) ^ 4 ≤ 10 ^ 27 by norm_num]
  have hlog : Real.log N = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]; push_cast; ring
  have hlogs : Real.log s ≤ s := (Real.log_le_sub_one_of_pos hs0).trans (by linarith)
  have hx : xOf N ^ 2 = s ^ 8 / c ^ 2 := by
    rw [xOf, div_pow, ← hs4]; ring
  rw [hx, hlog, ← hs2, ← hs4]
  have hc2 : c ^ 2 ≤ 4.0804 := by nlinarith [mul_le_mul hc1 hc1 hc0.le (by norm_num)]
  have hc2' : 0 < c ^ 2 := by positivity
  have lhs : 7.3306 * (s ^ 4 * s ^ 2) * (4 * Real.log s) ≤ 29.3224 * s ^ 7 := by
    have : s ^ 4 * s ^ 2 * Real.log s ≤ s ^ 4 * s ^ 2 * s :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    nlinarith
  have rhs : 0.048779 * s ^ 8 / (4.0804 * 49) ≤ (1.058259 - 1.00948) * (s ^ 8 / c ^ 2) / κ := by
    rw [κ]
    have : s ^ 8 / 4.0804 ≤ s ^ 8 / c ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hc2' hc2
    have h8 : 0 ≤ s ^ 8 := by positivity
    calc 0.048779 * s ^ 8 / (4.0804 * 49) = (1.058259 - 1.00948) * (s ^ 8 / 4.0804) / 49 := by
          ring
      _ ≤ _ := by gcongr
  have key : 29.3224 * s ^ 7 < 0.048779 * s ^ 8 / (4.0804 * 49) := by
    have h7 : 0 < s ^ 7 := by positivity
    have : s ^ 8 = s * s ^ 7 := by ring
    rw [this, lt_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right hsbig h7.le]
  linarith

/-- The final inequality with the cruder constant that comes from the easy sup-norm bounds
(`Helfgott/SupNorms.lean`) and elementary Chebyshev bounds (`Helfgott/Chebyshev.lean`): for `N ≥ 10²⁷`,
`6.7 · 10⁶ · N^{3/2} log N < (1.058259 - 1.00948) x²/κ`. -/
theorem final_inequality_crude (N : ℕ) (hN : 10 ^ 27 ≤ N) :
    6.7e6 * (N * √N) * Real.log N < (1.058259 - 1.00948) * xOf N ^ 2 / κ := by
  obtain ⟨hc0, hc1⟩ := xOf_denom_bounds
  set c := 2 + 9 / (196 * √(2 * Real.pi)) with hc
  have hNr : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNr
  -- `u = N^{1/16}`.
  set a := √(N : ℝ)
  set b := √a
  set d := √b
  set u := √d
  have ha : a ^ 2 = N := Real.sq_sqrt hN0.le
  have hb : b ^ 2 = a := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hd : d ^ 2 = b := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hu2 : u ^ 2 = d := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hu8 : u ^ 8 = a := by
    rw [show u ^ 8 = ((u ^ 2) ^ 2) ^ 2 by ring, hu2, hd, hb]
  have hu16 : u ^ 16 = (N : ℝ) := by
    rw [show u ^ 16 = (u ^ 8) ^ 2 by ring, hu8, ha]
  have hu0 : 0 < u := Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 hN0)))
  have hu48 : (48 : ℝ) ≤ u := by
    by_contra h
    push Not at h
    have : u ^ 16 < (48 : ℝ) ^ 16 := pow_lt_pow_left₀ h hu0.le (by norm_num)
    rw [hu16] at this
    linarith [show (48 : ℝ) ^ 16 ≤ 10 ^ 27 by norm_num]
  have hlog : Real.log N = 16 * Real.log u := by
    rw [← hu16, Real.log_pow]; push_cast; ring
  have hlogu : Real.log u ≤ u := (Real.log_le_sub_one_of_pos hu0).trans (by linarith)
  have hx : xOf N ^ 2 = u ^ 32 / c ^ 2 := by
    rw [xOf, div_pow, ← hu16]; ring
  rw [hx, hlog, ← hu8, ← hu16]
  have hc2 : c ^ 2 ≤ 4.0804 := by nlinarith [mul_le_mul hc1 hc1 hc0.le (by norm_num)]
  have hc2' : 0 < c ^ 2 := by positivity
  have lhs : 6.7e6 * (u ^ 16 * u ^ 8) * (16 * Real.log u) ≤ 1.072e8 * u ^ 25 := by
    have : u ^ 16 * u ^ 8 * Real.log u ≤ u ^ 16 * u ^ 8 * u :=
      mul_le_mul_of_nonneg_left hlogu (by positivity)
    nlinarith
  have rhs : 0.048779 * u ^ 32 / (4.0804 * 49) ≤
      (1.058259 - 1.00948) * (u ^ 32 / c ^ 2) / κ := by
    rw [κ]
    have : u ^ 32 / 4.0804 ≤ u ^ 32 / c ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hc2' hc2
    calc 0.048779 * u ^ 32 / (4.0804 * 49) = (1.058259 - 1.00948) * (u ^ 32 / 4.0804) / 49 := by
          ring
      _ ≤ _ := by gcongr
  have key : 1.072e8 * u ^ 25 < 0.048779 * u ^ 32 / (4.0804 * 49) := by
    have h25 : 0 < u ^ 25 := by positivity
    have h7 : (48 : ℝ) ^ 7 ≤ u ^ 7 := pow_le_pow_left₀ (by norm_num) hu48 7
    rw [show u ^ 32 = u ^ 7 * u ^ 25 by ring, lt_div_iff₀ (by norm_num)]
    nlinarith
  linarith

end TernaryGoldbach.Helfgott
