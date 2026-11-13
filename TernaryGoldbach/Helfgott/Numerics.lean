import TernaryGoldbach.Helfgott.Defs

/-!
# The final numerical inequality of [H, §14.4]

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

/-- The final inequality with the cruder constant that comes from the easy sup-norm bounds
(`Helfgott/SupNorms.lean`) and elementary Chebyshev bounds (`Helfgott/Chebyshev.lean`): for `N ≥ 10²⁷`,
`6.7 · 10⁶ · N^{3/2} log N < (1.049 - 1.0376) x²/κ`. -/
theorem final_inequality_crude (N : ℕ) (hN : 10 ^ 27 ≤ N) :
    6.7e6 * (N * √N) * Real.log N < (1.049 - 1.0376) * xOf N ^ 2 / κ := by
  obtain ⟨hc0, hc1⟩ := xOf_denom_bounds
  set c := 2 + 9 / (196 * √(2 * Real.pi)) with hc
  have hNr : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNr
  -- `v = N^{1/64}`.
  set a := √(N : ℝ)
  set b := √a
  set d := √b
  set f := √d
  set g := √f
  set v := √g
  have ha : a ^ 2 = N := Real.sq_sqrt hN0.le
  have hb : b ^ 2 = a := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hd : d ^ 2 = b := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hf : f ^ 2 = d := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hg : g ^ 2 = f := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hv : v ^ 2 = g := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hv32 : v ^ 32 = a := by
    rw [show v ^ 32 = ((((v ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 by ring, hv, hg, hf, hd, hb]
  have hv64 : v ^ 64 = (N : ℝ) := by
    rw [show v ^ 64 = (v ^ 32) ^ 2 by ring, hv32, ha]
  have hv0 : 0 < v := by
    have h1 : 0 < a := Real.sqrt_pos.2 hN0
    have h2 : 0 < b := Real.sqrt_pos.2 h1
    have h3 : 0 < d := Real.sqrt_pos.2 h2
    have h4 : 0 < f := Real.sqrt_pos.2 h3
    have h5 : 0 < g := Real.sqrt_pos.2 h4
    exact Real.sqrt_pos.2 h5
  have hvbig : (2.64 : ℝ) ≤ v := by
    by_contra h
    push Not at h
    have : v ^ 64 < (2.64 : ℝ) ^ 64 := pow_lt_pow_left₀ h hv0.le (by norm_num)
    rw [hv64] at this
    linarith [show (2.64 : ℝ) ^ 64 ≤ 10 ^ 27 by norm_num]
  have hlog : Real.log N = 64 * Real.log v := by
    rw [← hv64, Real.log_pow]; push_cast; ring
  -- `log v ≤ v/e ≤ v/2.7` (from `log(v/e) ≤ v/e - 1`).
  have hlogv : Real.log v ≤ v / 2.7 := by
    have he := Real.exp_one_gt_d9
    have he0 : 0 < Real.exp 1 := Real.exp_pos 1
    have h1 := Real.log_le_sub_one_of_pos (div_pos hv0 he0)
    rw [Real.log_div hv0.ne' he0.ne', Real.log_exp] at h1
    have : v / Real.exp 1 ≤ v / 2.7 := div_le_div_of_nonneg_left hv0.le (by norm_num) (by linarith)
    linarith
  have hx : xOf N ^ 2 = v ^ 128 / c ^ 2 := by
    rw [xOf, div_pow, ← hv64]; ring
  rw [hx, hlog, ← hv32, ← hv64]
  have hc2 : c ^ 2 ≤ 4.0804 := by nlinarith [mul_le_mul hc1 hc1 hc0.le (by norm_num)]
  have hc2' : 0 < c ^ 2 := by positivity
  have lhs : 6.7e6 * (v ^ 64 * v ^ 32) * (64 * Real.log v) ≤ 1.589e8 * v ^ 97 := by
    have : v ^ 64 * v ^ 32 * Real.log v ≤ v ^ 64 * v ^ 32 * (v / 2.7) :=
      mul_le_mul_of_nonneg_left hlogv (by positivity)
    have e : v ^ 64 * v ^ 32 * (v / 2.7) = v ^ 97 / 2.7 := by ring
    have h97 : 0 ≤ v ^ 97 := by positivity
    rw [e] at this
    rw [show 6.7e6 * (v ^ 64 * v ^ 32) * (64 * Real.log v) = 4.288e8 * (v ^ 64 * v ^ 32 * Real.log v)
      by ring]
    calc 4.288e8 * (v ^ 64 * v ^ 32 * Real.log v) ≤ 4.288e8 * (v ^ 97 / 2.7) := by gcongr
      _ ≤ 1.589e8 * v ^ 97 := by rw [mul_div_assoc']; rw [div_le_iff₀ (by norm_num)]; nlinarith
  have rhs : 0.0114 * v ^ 128 / (4.0804 * 49) ≤ (1.049 - 1.0376) * (v ^ 128 / c ^ 2) / κ := by
    rw [κ]
    have : v ^ 128 / 4.0804 ≤ v ^ 128 / c ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hc2' hc2
    calc 0.0114 * v ^ 128 / (4.0804 * 49) = (1.049 - 1.0376) * (v ^ 128 / 4.0804) / 49 := by
          ring
      _ ≤ _ := by gcongr
  have key : 1.589e8 * v ^ 97 < 0.0114 * v ^ 128 / (4.0804 * 49) := by
    have h97 : 0 < v ^ 97 := by positivity
    have h31 : (2.64 : ℝ) ^ 31 ≤ v ^ 31 := pow_le_pow_left₀ (by norm_num) hvbig 31
    rw [show v ^ 128 = v ^ 31 * v ^ 97 by ring, lt_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right h31 h97.le]
  linarith

end TernaryGoldbach.Helfgott
