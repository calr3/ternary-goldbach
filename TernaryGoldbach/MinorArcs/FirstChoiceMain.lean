import TernaryGoldbach.MinorArcs.FirstChoiceTypeII

/-!
# [B, §6.4, (6.76)–(6.77)]: the main term

`√(C(log t + 0.002) + log(4t)/2) · √(0.30214 log t + 0.7468) ≤ 0.27125 C log t + 0.41415 log t
+ 0.8764` (AM–GM with `√ρ = 1.84332`), using `C = C_{x,t} ≤ 0.1 log t + 0.14`.
[B] writes `0.49911` for the constant; the correct value is `0.81019…` (see `PointwiseBound.lean`).
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- `C_{x,t} ≤ 0.1 log t + 0.14` for `T ≥ 6·10⁶`, `2 ≤ t ≤ T/3`. -/
theorem Cxt_le {T t : ℝ} (hT : 6e6 ≤ T) (ht2 : 2 ≤ t) (htT : t ≤ T / 3) :
    Cxt T t ≤ 0.1 * Real.log t + 0.14 := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have he := Real.exp_one_lt_d9
  set L := Real.log (9 * T / (2.004 * t)) with hL
  set u := Real.log t with hu
  have hl4 : Real.log (4 * t) = 2 * Real.log 2 + u := by
    rw [Real.log_mul (by norm_num) ht0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlog2 := Real.log_two_lt_d9
  have hu0 : 0 ≤ u := Real.log_nonneg (by linarith)
  -- `L ≥ 2.6`.
  have hL26 : 2.6 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have h1 : rexp 2.6 ≤ 13.47 := by
      have : rexp 2.6 ^ 5 ≤ 13.47 ^ 5 := by
        rw [← Real.exp_nat_mul]
        calc rexp ((5 : ℕ) * 2.6) = rexp 1 ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 13 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 13
          _ ≤ 13.47 ^ 5 := by norm_num
      exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) this
    refine h1.trans ?_
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hl40 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  set z := Real.log (4 * t) / (2 * L) with hz_def
  have hz0 : 0 ≤ z := by positivity
  have hCdef : Cxt T t = Real.log (1 + z) := by unfold Cxt; rw [← hL]
  have hCz : Cxt T t ≤ z := by
    rw [hCdef]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + z by linarith)
    linarith
  rcases le_or_gt 5 L with h5 | h5
  · -- `C ≤ log(4t)/10`.
    have : z ≤ Real.log (4 * t) / 10 :=
      div_le_div_of_nonneg_left hl40 (by norm_num) (by linarith)
    linarith
  · -- `L < 5` forces `log t ≥ 12.1`.
    have hu12 : 12.1 ≤ u := by
      have h1 : 9 * T / (2.004 * t) < rexp 5 := by
        rw [hL] at h5; exact (Real.log_lt_iff_lt_exp (by positivity)).1 h5
      have h2 : rexp 5 ≤ 148.42 := by
        calc rexp 5 = rexp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 5
          _ ≤ 148.42 := by norm_num
      have h3 : 181500 ≤ t := by
        rw [div_lt_iff₀ (by positivity)] at h1
        have := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ 2.004 * t by positivity)
        linarith
      rw [hu, Real.le_log_iff_exp_le ht0]
      have : rexp 12.1 ≤ 181500 := by
        have : rexp 12.1 ^ 10 ≤ 181500 ^ 10 := by
          rw [← Real.exp_nat_mul]
          calc rexp ((10 : ℕ) * 12.1) = rexp 1 ^ 121 := by rw [← Real.exp_nat_mul]; norm_num
            _ ≤ 2.7182818286 ^ 121 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 121
            _ ≤ 181500 ^ 10 := by norm_num
        exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) this
      linarith
    have hz : z ≤ (u + 1.3863) / 5.2 := by
      rw [hz_def, div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    -- `log(1 + z) ≤ log 3.6 + (1 + z - 3.6)/3.6`, `log 3.6 ≤ 1.2863`.
    have h36 : Real.log 3.6 ≤ 1.2863 := by
      have e : (3.6 : ℝ) = 4 * 0.9 := by norm_num
      rw [e, Real.log_mul (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.log_pow]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 0.9 by norm_num)
      push_cast; linarith
    have htan : Cxt T t ≤ Real.log 3.6 + (1 + z - 3.6) / 3.6 := by
      rw [hCdef]
      have := Real.log_le_sub_one_of_pos (show 0 < (1 + z) / 3.6 by positivity)
      rw [Real.log_div (by linarith) (by norm_num)] at this
      have e : (1 + z - 3.6) / 3.6 = (1 + z) / 3.6 - 1 := by ring
      rw [e]; linarith
    have h7 : (1 + z - 3.6) / 3.6 ≤ (1 + (u + 1.3863) / 5.2 - 3.6) / 3.6 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have e2 : (1 + (u + 1.3863) / 5.2 - 3.6) / 3.6 = u / 18.72 + (1.3863 / 5.2 - 2.6) / 3.6 := by
      ring
    have h8 : (1.3863 / 5.2 - 2.6 : ℝ) / 3.6 ≤ -0.6481 := by norm_num
    have h9 : u / 18.72 ≤ 0.05342 * u := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith

/-- `√a √b ≤ (a/s + s b)/2`. -/
theorem sqrt_mul_sqrt_le {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) :
    √a * √b ≤ (a / s + s * b) / 2 := by
  rw [← Real.sqrt_mul ha]
  rw [Real.sqrt_le_left (by positivity)]
  have : (a / s + s * b) ^ 2 - 4 * (a * b) = (a / s - s * b) ^ 2 := by field_simp; ring
  nlinarith [sq_nonneg (a / s - s * b)]

/-- **[B, (6.77)], corrected**: the main term is at most `R_{x,t} log t + 0.8764`. -/
theorem main_amgm {T t : ℝ} (hT : 6e6 ≤ T) (ht2 : 2 ≤ t) (htT : t ≤ T / 3) (hC0 : 0 ≤ Cxt T t) :
    √(Cxt T t * (Real.log t + 0.002) + Real.log (4 * t) / 2) *
        √(0.30214 * Real.log t + 0.7468) ≤
      (0.27125 * Cxt T t + 0.41415) * Real.log t + 0.8764 := by
  have ht0 : 0 < t := by linarith
  have hu0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hl4 : Real.log (4 * t) = 2 * Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num) ht0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hC := Cxt_le hT ht2 htT
  have h := sqrt_mul_sqrt_le (s := 1.84332) (a := Cxt T t * (Real.log t + 0.002) + Real.log (4 * t) / 2)
    (b := 0.30214 * Real.log t + 0.7468) (by rw [hl4]; positivity) (by positivity) (by norm_num)
  refine h.trans ?_
  rw [hl4]
  have e : ((Cxt T t * (Real.log t + 0.002) + (2 * Real.log 2 + Real.log t) / 2) / 1.84332 +
      1.84332 * (0.30214 * Real.log t + 0.7468)) / 2 =
      Cxt T t * Real.log t / 3.68664 + 0.002 * Cxt T t / 3.68664 + Real.log 2 / 3.68664 +
      (1 / 7.37328 + 1.84332 * 0.30214 / 2) * Real.log t + 1.84332 * 0.7468 / 2 := by
    field_simp; ring
  rw [e]
  have h1 : Cxt T t * Real.log t / 3.68664 ≤ 0.27125 * Cxt T t * Real.log t := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith [mul_nonneg hC0 hu0]
  have h2 : 0.002 * Cxt T t / 3.68664 ≤ 0.0005425 * (0.1 * Real.log t + 0.14) := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  have h3 : Real.log 2 / 3.68664 ≤ 0.6931471808 / 3.68664 :=
    div_le_div_of_nonneg_right hlog2.le (by norm_num)
  have e2 : (0.27125 * Cxt T t + 0.41415) * Real.log t + 0.8764 =
      0.27125 * Cxt T t * Real.log t + 0.41415 * Real.log t + 0.8764 := by ring
  rw [e2]
  have h4 : (1 / 7.37328 + 1.84332 * 0.30214 / 2) * Real.log t + 0.0005425 * (0.1 * Real.log t) ≤
      0.41415 * Real.log t := by
    have : ((1 / 7.37328 + 1.84332 * 0.30214 / 2) + 0.0005425 * 0.1 : ℝ) ≤ 0.41415 := by norm_num
    nlinarith
  have h5 : (0.6931471808 / 3.68664 + 1.84332 * 0.7468 / 2 + 0.0005425 * 0.14 : ℝ) ≤ 0.8764 := by
    norm_num
  linarith

end TernaryGoldbach.MinorArcs
