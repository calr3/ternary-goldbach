import TernaryGoldbach.MinorArcs.FirstChoiceTypeI2

/-!
# [B, §6.3.1, (6.59)]: `S_{I,2}` at the first choice of parameters, assembled
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- `2√(c₀c)/π ≤ 3.57424 √c`. -/
theorem two_sqrt_c0_mul_le {c : ℝ} (hc : 0 ≤ c) : 2 * √(c₀ * c) / π ≤ 3.57424 * √c := by
  obtain ⟨hc0a, hc0b⟩ := sqrt_c₀_bounds
  have hpi := Real.pi_gt_d6
  rw [Real.sqrt_mul (by norm_num [c₀]) c, div_le_iff₀ (by linarith)]
  have hs := Real.sqrt_nonneg c
  have : 3.57424 * √c * 3.141592 ≤ 3.57424 * √c * π := mul_le_mul_of_nonneg_left hpi.le (by positivity)
  nlinarith

set_option maxHeartbeats 1600000 in
/-- The rest of `S_{I,2}` for `|δ| ≥ 1/2c₂` ([B, (6.14)], `ε = 0.07`) at the parameters:
`≤ 2.4916 x/√t + (13.663 log t + 19.84) · 2x/t + 0.552 x^{5/6}`. -/
theorem typeI2_large_rest_first {δ T : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : 1 ≤ q)
    (hqT : (q : ℝ) ≤ T / 6) (ht2 : 2 ≤ delta0 δ * q) (htT : delta0 δ * q ≤ T / 3)
    (hδ : 1 / (2 * c₂) ≤ |δ|) :
    let t := delta0 δ * q
    let U := (U1 T t : ℝ)
    let V := (V1 T : ℝ)
    let c := cPlus (T ^ 3) U V
    1.0004 * (2 * √(c₀ * c) / π * (1 + (1 + 0.07) * (1 + V / (3 / 4 * T ^ 2)) / rexp 1)) * (U * V) +
        1.0004 * (3 / 2 * c * (2 + (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3))) *
          (T ^ 3 * V / (3 / 4 * T ^ 2)) +
        1.0004 * (35 * c₀ * c₂ / (3 * π ^ 2)) * (3 / 4 * T ^ 2) +
        2 * √(c₀ * c) / π * (1 + 0.07) * √(3 + 2 * 0.07) *
          (T ^ 3 / (|δ| * q) * (1.03883 + Real.log q + logPlus (6 * U * V * |δ| * q / (√2 * T ^ 3))) +
            1.0004 * V) ≤
      2.4916 * (T ^ 3 / √t) + (13.663 * Real.log t + 19.84) * (2 * T ^ 3 / t) +
        0.552 * (T ^ 2 * √T) := by
  intro t U V c
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hst : 0 < √t := Real.sqrt_pos.2 ht0
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsT := sqrt_ge_2449 hT
  obtain ⟨hc1, hc2⟩ := cPlus_first hT ht0
  have hc3 := cPlus_le_296 hT ht2
  have hsc := sqrt_cPlus_first hT ht0
  have he' := Real.exp_one_gt_d9
  have he := Real.exp_one_lt_d9
  have hUV : U * V ≤ T ^ 3 / (2 * √t) := U1V1_le hT0 ht0
  have hUV0 : 0 ≤ U * V := by positivity
  have hV1 : 9 * T / 2 - 1 ≤ V := V1_ge hT0
  have hV2 : V ≤ 9 * T / 2 := V1_le hT0
  have hV0 : 0 ≤ V := by linarith
  have hsc0 : 0 ≤ √c := Real.sqrt_nonneg _
  have hA := two_sqrt_c0_mul_le (show 0 ≤ c by linarith)
  have hA0 : 0 ≤ 2 * √(c₀ * c) / π := by positivity
  have hss : √t * √t = t := Real.mul_self_sqrt ht0.le
  obtain ⟨hlt, h1t⟩ := log_div_sqrt_le ht2
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  -- B5.
  have hVQ : V / (3 / 4 * T ^ 2) ≤ 1e-6 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hB5 : 1.0004 * (2 * √(c₀ * c) / π * (1 + (1 + 0.07) * (1 + V / (3 / 4 * T ^ 2)) / rexp 1)) *
      (U * V) ≤ 2.4916 * (T ^ 3 / √t) + 1.7271 * (2 * T ^ 3 / t) := by
    have hf : 1 + (1 + 0.07) * (1 + V / (3 / 4 * T ^ 2)) / rexp 1 ≤ 1.393634 := by
      have : (1 + 0.07) * (1 + V / (3 / 4 * T ^ 2)) / rexp 1 ≤ 1.07 * (1 + 1e-6) / 2.7182818283 := by
        gcongr; norm_num
      have : (1.07 * (1 + 1e-6) / 2.7182818283 : ℝ) ≤ 0.393634 := by norm_num
      linarith
    have hf0 : 0 ≤ 1 + (1 + 0.07) * (1 + V / (3 / 4 * T ^ 2)) / rexp 1 := by positivity
    calc _ ≤ 1.0004 * (3.57424 * (1 + 1.3863 / √t) * 1.393634) * (T ^ 3 / (2 * √t)) := by
          gcongr
          exact hA.trans (by gcongr)
      _ = 1.0004 * 3.57424 * 1.393634 / 2 * (T ^ 3 / √t) +
          1.0004 * 3.57424 * 1.393634 * 1.3863 / 4 * (2 * T ^ 3 / (√t * √t)) := by field_simp; ring
      _ ≤ _ := by
          rw [hss]
          have : 0 ≤ T ^ 3 / √t := by positivity
          have : 0 ≤ 2 * T ^ 3 / t := by positivity
          gcongr <;> norm_num
  -- B6.
  have hlog := log_le_sqrt_sharp hT
  have hB6 : 1.0004 * (3 / 2 * c * (2 + (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3))) *
      (T ^ 3 * V / (3 / 4 * T ^ 2)) ≤ 0.5436 * (T ^ 2 * √T) := by
    have hd := delta0_ge δ
    have hδq : |δ| * q ≤ 4 * t := by
      have : |δ| / 4 ≤ delta0 δ := le_max_right _ _
      show |δ| * q ≤ 4 * (delta0 δ * q)
      nlinarith
    have harg : 2 * U * V * |δ| * q / T ^ 3 ≤ 4 * √t := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 2 * (U * V) * (|δ| * q) ≤ 2 * (T ^ 3 / (2 * √t)) * (4 * t) := by gcongr
      have h2 : 2 * (T ^ 3 / (2 * √t)) * (4 * t) = 4 * √t * T ^ 3 := by
        rw [show 2 * (T ^ 3 / (2 * √t)) * (4 * t) = 4 * T ^ 3 * (t / √t) by field_simp,
          Real.div_sqrt]; ring
      nlinarith
    have harg0 : 0 ≤ 2 * U * V * |δ| * q / T ^ 3 := by
      rw [show 2 * U * V * |δ| * q = 2 * (U * V) * |δ| * q by ring]; positivity
    have h4w : 1 ≤ 4 * √t := by
      have : 1.4142 ≤ √t := by rw [Real.le_sqrt (by norm_num) ht0.le]; nlinarith
      linarith
    have hL : logPlus (2 * U * V * |δ| * q / T ^ 3) ≤ 1.3863 + Real.log √t := by
      refine (logPlus_le_log_of_le' harg0 harg h4w).trans ?_
      rw [Real.log_mul (by norm_num) hst.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_lt_d9; push_cast; linarith
    have hL0 := logPlus_nonneg (2 * U * V * |δ| * q / T ^ 3)
    -- `c (2 + 15.2858 L) ≤ 16.985 + 0.053436 √T`.
    have hw := log_le_div_exp hst
    have hwT : Real.log √t ≤ 0.0032 * √T - 0.5 := by
      have h1 : Real.log √t = Real.log t / 2 := Real.log_sqrt ht0.le
      have h2 : Real.log t ≤ Real.log T - 1 := by
        have : Real.log t ≤ Real.log (T / 3) := Real.log_le_log ht0 htT
        rw [Real.log_div hT0.ne' (by norm_num)] at this
        have : 1 ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]; linarith
        linarith
      rw [h1]; linarith
    have hwl0 : 0 ≤ Real.log √t := Real.log_nonneg (by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith))
    have hcP : c * (2 + (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3)) ≤
        16.985 + 0.053436 * √T := by
      have hk : (1 + 0.07) / 0.07 ≤ (15.2858 : ℝ) := by norm_num
      have hP : 2 + (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3) ≤
          23.191 + 15.2858 * Real.log √t := by
        have : (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3) ≤
            15.2858 * (1.3863 + Real.log √t) :=
          mul_le_mul hk hL hL0 (by norm_num)
        linarith
      have hP0 : 0 ≤ 2 + (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3) := by positivity
      rcases le_total 30 √t with hw30 | hw30
      · have hc30 : c ≤ 1.09242 := by
          have : 2.7726 / √t ≤ 2.7726 / 30 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw30
          have : (2.7726 : ℝ) / 30 ≤ 0.09242 := by norm_num
          linarith
        calc _ ≤ 1.09242 * (23.191 + 15.2858 * Real.log √t) := mul_le_mul hc30 hP hP0 (by norm_num)
          _ ≤ 16.985 + 0.053436 * √T := by nlinarith
      · have hl30 : Real.log √t ≤ 3.4033 := by
          have h1 : Real.log √t ≤ Real.log 30 := Real.log_le_log hst hw30
          have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 30 / 32 by norm_num)
          rw [Real.log_div (by norm_num) (by norm_num), show (32 : ℝ) = 2 ^ 5 by norm_num,
            Real.log_pow] at h2
          have := Real.log_two_lt_d9
          push_cast at h2; linarith
        -- `c P ≤ P + 2.7726 P/√t`, `P/√t ≤ 23.191/1.4142 + 15.2858·0.36788`.
        have hs14 : 1.4142 ≤ √t := by rw [Real.le_sqrt (by norm_num) ht0.le]; nlinarith
        have hPw : (23.191 + 15.2858 * Real.log √t) / √t ≤ 22.03 := by
          rw [div_le_iff₀ hst]
          have : √t / rexp 1 ≤ 0.36788 * √t := by
            rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
          nlinarith
        have : c * (2 + (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3)) ≤
            (1 + 2.7726 / √t) * (23.191 + 15.2858 * Real.log √t) :=
          mul_le_mul hc2 hP hP0 (by positivity)
        have e : (1 + 2.7726 / √t) * (23.191 + 15.2858 * Real.log √t) =
            (23.191 + 15.2858 * Real.log √t) + 2.7726 * ((23.191 + 15.2858 * Real.log √t) / √t) := by
          field_simp
        nlinarith
    have hxVQ : T ^ 3 * V / (3 / 4 * T ^ 2) ≤ 6 * T ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [pow_pos hT0 3]
    calc _ = 1.0004 * 1.5 * (c * (2 + (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3))) *
          (T ^ 3 * V / (3 / 4 * T ^ 2)) := by ring
      _ ≤ 1.0004 * 1.5 * (16.985 + 0.053436 * √T) * (6 * T ^ 2) := by
          have : 0 ≤ T ^ 3 * V / (3 / 4 * T ^ 2) := by positivity
          have : 0 ≤ c * (2 + (1 + 0.07) / 0.07 * logPlus (2 * U * V * |δ| * q / T ^ 3)) := by
            have := logPlus_nonneg (2 * U * V * |δ| * q / T ^ 3)
            have : 0 ≤ c := by linarith
            positivity
          gcongr
      _ ≤ 0.5436 * (T ^ 2 * √T) := by
          have : 2449 * T ^ 2 ≤ T ^ 2 * √T := by nlinarith [pow_pos hT0 2]
          nlinarith [pow_pos hT0 2]
  -- B7.
  have hB7 : 1.0004 * (35 * c₀ * c₂ / (3 * π ^ 2)) * (3 / 4 * T ^ 2) ≤ 0.0077 * (T ^ 2 * √T) := by
    have e : 35 * c₀ * c₂ / (3 * π ^ 2) = 7 * (5 * c₀ * c₂ / (3 * π ^ 2)) := by ring
    rw [e, c₂_identity]
    obtain ⟨hc0a, hc0b⟩ := sqrt_c₀_bounds
    have hpi := Real.pi_gt_d6
    have : 2 * √c₀ / π ≤ 3.57424 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have : 0 ≤ 2 * √c₀ / π := by positivity
    calc 1.0004 * (7 * (2 * √c₀ / π)) * (3 / 4 * T ^ 2) ≤ 1.0004 * (7 * 3.57424) * (3 / 4 * T ^ 2) := by
          gcongr
      _ ≤ 0.0077 * (T ^ 2 * √T) := by
          have : 2449 * T ^ 2 ≤ T ^ 2 * √T := by nlinarith [pow_pos hT0 2]
          nlinarith [pow_pos hT0 2]
  -- B8.
  have hB8 : 2 * √(c₀ * c) / π * (1 + 0.07) * √(3 + 2 * 0.07) *
      (T ^ 3 / (|δ| * q) * (1.03883 + Real.log q + logPlus (6 * U * V * |δ| * q / (√2 * T ^ 3))) +
        1.0004 * V) ≤ (13.663 * Real.log t + 18.111) * (2 * T ^ 3 / t) + 0.0001 * (T ^ 2 * √T) := by
    have hD : 2 * √(c₀ * c) / π * (1 + 0.07) * √(3 + 2 * 0.07) ≤ 6.77695 * (1 + 1.3863 / √t) := by
      have h1 : √(3 + 2 * 0.07 : ℝ) ≤ 1.77201 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      calc _ ≤ 3.57424 * (1 + 1.3863 / √t) * (1 + 0.07) * 1.77201 := by
            gcongr; exact hA.trans (by gcongr)
        _ ≤ 6.77695 * (1 + 1.3863 / √t) := by
            have : 0 ≤ 1 + 1.3863 / √t := by positivity
            nlinarith
    have hD0 : 0 ≤ 2 * √(c₀ * c) / π * (1 + 0.07) * √(3 + 2 * 0.07) := by positivity
    have hx := typeI2_B8x_first (x := T ^ 3) (U := U) (V := V) hq (by positivity) hδ hUV0 hUV
    have hx0 : 0 ≤ T ^ 3 / (|δ| * q) * (1.03883 + Real.log q +
        logPlus (6 * U * V * |δ| * q / (√2 * T ^ 3))) := by
      have := logPlus_nonneg (6 * U * V * |δ| * q / (√2 * T ^ 3))
      have := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
      positivity
    have hsc2 : 1 + 1.3863 / √t ≤ 1.9804 := by
      have : 1.3863 / √t = 1.3863 * (1 / √t) := by ring
      nlinarith
    calc _ ≤ 6.77695 * (1 + 1.3863 / √t) * ((2.016 * Real.log t + 0.3108) * (2 * T ^ 3 / t) +
          1.0004 * (9 * T / 2)) := by gcongr
      _ = 6.77695 * (2.016 * Real.log t + 0.3108 + 1.3863 * 2.016 * (Real.log t / √t) +
            1.3863 * 0.3108 * (1 / √t)) * (2 * T ^ 3 / t) +
          6.77695 * (1 + 1.3863 / √t) * (1.0004 * (9 * T / 2)) := by
          field_simp; ring
      _ ≤ 6.77695 * (2.016 * Real.log t + 0.3108 + 1.3863 * 2.016 * 0.7358 +
            1.3863 * 0.3108 * 0.7072) * (2 * T ^ 3 / t) +
          6.77695 * 1.9804 * (1.0004 * (9 * T / 2)) := by
          have : 0 ≤ 2 * T ^ 3 / t := by positivity
          gcongr
      _ ≤ _ := by
          have h0 : 0 ≤ 2 * T ^ 3 / t := by positivity
          have h1 : 6.77695 * (2.016 * Real.log t + 0.3108 + 1.3863 * 2.016 * 0.7358 +
              1.3863 * 0.3108 * 0.7072) ≤ 13.663 * Real.log t + 18.111 := by nlinarith
          have h2 : 6.77695 * 1.9804 * (1.0004 * (9 * T / 2)) ≤ 0.0001 * (T ^ 2 * √T) := by
            have : 2449 * T ≤ T * √T := by nlinarith
            have : 6e6 * (T * √T) ≤ T ^ 2 * √T := by
              have : 0 ≤ T * √T := by positivity
              nlinarith
            nlinarith
          nlinarith
  have : 0 ≤ T ^ 2 * √T := by positivity
  have : 0 ≤ 2 * T ^ 3 / t := by positivity
  nlinarith

end TernaryGoldbach.MinorArcs
