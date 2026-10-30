import TernaryGoldbach.MinorArcs.FirstChoiceTypeI1

/-!
# [B, §6.3.1, (6.57)–(6.59)]: `S_{I,2}` at the first choice of parameters

`|S_{I,2}| ≤ 2.4916 x/√t + 0.8 · 2x/(δ₀φ(q)) + (15.17 log t + 21.3) · 2x/t + 0.56 x^{5/6}`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- `log T ≤ 0.0064 √T` for `T ≥ 6·10⁶`. -/
theorem log_le_sqrt_sharp {T : ℝ} (hT : 6e6 ≤ T) : Real.log T ≤ 0.0064 * √T := by
  have hT0 : 0 < T := by linarith
  have hsT := sqrt_ge_2449 hT
  set u := √T
  have hu0 : 0 < u := by linarith
  have h1 : Real.log T = 2 * Real.log u := by
    rw [← Real.log_rpow hu0, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt hT0.le]
  -- `log u ≤ log 2449 + (u/2449 - 1)`, `log 2449 ≤ 11 log 2 + (2449/2048 - 1)`.
  have h2 := Real.log_le_sub_one_of_pos (show 0 < u / 2449 by positivity)
  rw [Real.log_div hu0.ne' (by norm_num)] at h2
  have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2449 / 2048 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), show (2048 : ℝ) = 2 ^ 11 by norm_num,
    Real.log_pow] at h3
  have := Real.log_two_lt_d9
  push_cast at h3
  rw [h1]
  nlinarith

theorem sqrt_le_one_add_half {c : ℝ} (hc : 0 ≤ c) : √c ≤ 1 + (c - 1) / 2 := by
  rw [Real.sqrt_le_left (by
    rcases le_total 1 c with h | h
    · linarith
    · nlinarith [Real.sqrt_nonneg c])]
  · nlinarith [sq_nonneg (c - 1)]

/-- `c₊ ≤ 1 + 2.7726/√t`. -/
theorem cPlus_first {T t : ℝ} (hT : 6e6 ≤ T) (ht : 0 < t) :
    1 ≤ cPlus (T ^ 3) (U1 T t) (V1 T) ∧ cPlus (T ^ 3) (U1 T t) (V1 T) ≤ 1 + 2.7726 / √t := by
  have hT0 : 0 < T := by linarith
  have hUV := U1V1_le hT0 ht
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hη := eta2'L1_le
  have hη0 := eta2'L1_pos
  unfold cPlus
  constructor
  · have : 0 ≤ eta2'L1 / (T ^ 3 / ((U1 T t : ℝ) * V1 T)) := by positivity
    linarith
  · rcases (show (0 : ℝ) ≤ (U1 T t : ℝ) * V1 T by positivity).lt_or_eq with h | h
    · rw [div_div_eq_mul_div]
      have : eta2'L1 * ((U1 T t : ℝ) * V1 T) / T ^ 3 ≤ 5.5452 * (T ^ 3 / (2 * √t)) / T ^ 3 := by
        gcongr
      have e : 5.5452 * (T ^ 3 / (2 * √t)) / T ^ 3 = 2.7726 / √t := by field_simp; norm_num
      linarith
    · rw [← h]; simp; positivity

theorem sqrt_cPlus_first {T t : ℝ} (hT : 6e6 ≤ T) (ht : 0 < t) :
    √(cPlus (T ^ 3) (U1 T t) (V1 T)) ≤ 1 + 1.3863 / √t := by
  obtain ⟨h1, h2⟩ := cPlus_first hT ht
  refine (sqrt_le_one_add_half (by linarith)).trans ?_
  have : 2.7726 / √t / 2 = 1.3863 / √t := by ring
  linarith

theorem log_div_sqrt_le {t : ℝ} (ht : 2 ≤ t) :
    Real.log t / √t ≤ 0.7358 ∧ 1 / √t ≤ 0.7072 := by
  have ht0 : 0 < t := by linarith
  have hst : 0 < √t := Real.sqrt_pos.2 ht0
  have h2 : 1.4142 ≤ √t := by
    rw [Real.le_sqrt (by norm_num) ht0.le]; nlinarith
  constructor
  · have h1 : Real.log t = 2 * Real.log √t := by
      rw [← Real.log_rpow hst, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast,
        Real.sq_sqrt ht0.le]
    have h3 := log_le_div_exp hst
    have h4 : (2.71828 : ℝ) ≤ rexp 1 := by have := Real.exp_one_gt_d9; linarith
    have h5 : √t / rexp 1 ≤ √t / 2.71828 := div_le_div_of_nonneg_left hst.le (by norm_num) h4
    rw [h1, div_le_iff₀ hst]
    have : √t / 2.71828 ≤ 0.36788 * √t := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    nlinarith
  · rw [div_le_iff₀ hst]; nlinarith

theorem log_108_le : Real.log 108 ≤ 4.696 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 108 / 128 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), show (128 : ℝ) = 2 ^ 7 by norm_num,
    Real.log_pow] at h
  have := Real.log_two_lt_d9
  push_cast at h; linarith

/-- The `μ`-term of `S_{I,2}` ([B, (6.57)]) at the parameters: with `min(1,a/ℓ)(ℓ + b) ≤ a + b`,
`≤ 0.8 · 2x/(δ₀φ(q)) + (1.5 log t + 1.309) · 2x/t`. -/
theorem typeI2_mu_first {δ T : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : 1 ≤ q)
    (ht2 : 2 ≤ delta0 δ * q) (htT : delta0 δ * q ≤ T / 3) :
    T ^ 3 / (2 * q) * minInv c₀ (π * δ) *
        muBound (min (3 / 4 * T ^ 2 / (2 * V1 T)) (U1 T (delta0 δ * q))) q *
        Real.log (V1 T * q) ≤
      0.8 * (2 * T ^ 3 / (delta0 δ * Nat.totient q)) +
        (1.5 * Real.log (delta0 δ * q) + 1.309) * (2 * T ^ 3 / (delta0 δ * q)) := by
  set t := delta0 δ * q with ht
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hd := delta0_ge δ
  have hqt : 2 * (q : ℝ) ≤ t := by rw [ht]; nlinarith
  have hV1 := V1_ge hT0
  have hV2 := V1_le hT0
  have hV0 : (0 : ℝ) < V1 T := by linarith
  have hU := U1_ge hT ht0 htT
  have hsT := sqrt_ge_2449 hT
  set M₀ := min (3 / 4 * T ^ 2 / (2 * V1 T)) (U1 T t : ℝ) with hM₀
  have hM₀ : T / 12 ≤ M₀ := by
    refine le_min ?_ ?_
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · nlinarith
  have hM0 : 0 < M₀ := by linarith
  have hL0 : 0 ≤ Real.log (V1 T * q) := Real.log_nonneg (by nlinarith)
  have hmu := muBound_mul_le hq hM0 hL0 (M := M₀)
  have hmax : max (Real.log (V1 T * q) - Real.log (M₀ / (2 * q ^ 2))) 0 ≤
      4.696 + 3 * Real.log q := by
    have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
    refine max_le ?_ (by linarith)
    rw [← Real.log_div (by positivity) (by positivity)]
    have h1 : V1 T * q / (M₀ / (2 * q ^ 2)) ≤ 108 * q ^ 3 := by
      rw [div_le_iff₀ (by positivity)]
      have : (V1 T : ℝ) * q * (2 * q ^ 2) ≤ 9 * T / 2 * q * (2 * q ^ 2) := by gcongr
      have e : 108 * (q : ℝ) ^ 3 * (M₀ / (2 * q ^ 2)) = 54 * q * M₀ := by field_simp; ring
      rw [e]
      have : 54 * (q : ℝ) * (T / 12) ≤ 54 * q * M₀ := by gcongr
      have : (V1 T : ℝ) * q ≤ 9 * T / 2 * q := by gcongr
      linarith
    calc Real.log (V1 T * q / (M₀ / (2 * q ^ 2))) ≤ Real.log (108 * q ^ 3) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log 108 + 3 * Real.log q := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by linarith [log_108_le]
  have hm0 : 0 ≤ minInv c₀ (π * δ) := by
    unfold minInv; split_ifs
    · norm_num
    · exact le_min zero_le_one (div_nonneg (by norm_num [c₀]) (sq_nonneg _))
  have hx0 : (0 : ℝ) ≤ T ^ 3 := by positivity
  have hA := xphi_le (x := T ^ 3) (δ := δ) hx0 hq
  have hB := xq_le (x := T ^ 3) (δ := δ) hx0 hq
  rw [← ht] at hB
  have hc0 : 0 ≤ T ^ 3 / (2 * q) * minInv c₀ (π * δ) := by positivity
  have hlogq : Real.log q ≤ Real.log t - 0.6931 := by
    have h1 : Real.log q ≤ Real.log (t / 2) := Real.log_le_log hq0 (by linarith)
    rw [Real.log_div ht0.ne' (by norm_num)] at h1
    have := Real.log_two_gt_d9; linarith
  calc T ^ 3 / (2 * q) * minInv c₀ (π * δ) * muBound M₀ q * Real.log (V1 T * q)
      = T ^ 3 / (2 * q) * minInv c₀ (π * δ) * (muBound M₀ q * Real.log (V1 T * q)) := by ring
    _ ≤ T ^ 3 / (2 * q) * minInv c₀ (π * δ) *
        (4 / 5 * (2 * q / Nat.totient (2 * q)) + (4.696 + 3 * Real.log q)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
    _ = 0.8 * (T ^ 3 / (2 * q) * minInv c₀ (π * δ) * (2 * q / Nat.totient (2 * q))) +
        (4.696 + 3 * Real.log q) * (T ^ 3 / (2 * q) * minInv c₀ (π * δ)) := by ring
    _ ≤ 0.8 * (2 * T ^ 3 / (delta0 δ * Nat.totient q)) + (4.696 + 3 * Real.log q) * (T ^ 3 / t) := by
        have : 0 ≤ 4.696 + 3 * Real.log q := by have := Real.log_nonneg hq1; linarith
        gcongr
    _ ≤ _ := by
        have e : (1.5 * Real.log t + 1.309) * (2 * T ^ 3 / t) = (3 * Real.log t + 2.618) * (T ^ 3 / t) := by
          field_simp; ring
        rw [e]
        have : 0 ≤ T ^ 3 / t := by positivity
        have : 4.696 + 3 * Real.log q ≤ 3 * Real.log t + 2.618 := by linarith
        gcongr

/-- The `c₀(1/8 - 1/2π²)` term of `S_{I,2}` at the parameters: `≤ 0.1466 · 2x/t + 0.0005 x^{5/6}`. -/
theorem typeI2_c0_first {T t : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : 1 ≤ q) (hqT : (q : ℝ) ≤ T / 6)
    (ht2 : 2 ≤ t) (htT : t ≤ T / 3) :
    c₀ * (1 / 8 - 1 / (2 * π ^ 2)) / T ^ 3 *
        ((U1 T t : ℝ) ^ 2 / q * (0.5004 * (V1 T : ℝ) ^ 2 + V1 T * q * Real.log q) +
          (2 * U1 T t + q) * (0.5004 * (V1 T : ℝ) ^ 2)) ≤
      0.1466 * (2 * T ^ 3 / t) + 0.0005 * (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsT := sqrt_ge_2449 hT
  have hst : 0 < √t := Real.sqrt_pos.2 ht0
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  set K₀ := c₀ * (1 / 8 - 1 / (2 * π ^ 2)) with hK₀
  have hK1 : K₀ ≤ 2.3433 := by
    rw [hK₀]; have : c₀ = 31.521 := rfl
    rw [this]
    have : 1 / (2 * π ^ 2) ≥ 1 / (2 * 3.1416 ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    have : (1 : ℝ) / (2 * 3.1416 ^ 2) ≥ 0.05066 := by norm_num
    nlinarith
  have hK0 : 0 ≤ K₀ := by
    rw [hK₀]
    have : 1 / (2 * π ^ 2) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have : (0 : ℝ) < c₀ := by norm_num [c₀]
    have : 0 ≤ 1 / 8 - 1 / (2 * π ^ 2) := by linarith
    positivity
  set U := (U1 T t : ℝ)
  set V := (V1 T : ℝ)
  have hU0 : 0 ≤ U := Nat.cast_nonneg _
  have hV0 : 0 ≤ V := Nat.cast_nonneg _
  have hUV : U * V ≤ T ^ 3 / (2 * √t) := U1V1_le hT0 ht0
  have hV2 : V ≤ 9 * T / 2 := V1_le hT0
  have hU2 : U ≤ 0.0786 * T ^ 2 := by
    refine (U1_le (T := T) ht0).trans ?_
    have h1 : √2 ≤ √t := Real.sqrt_le_sqrt ht2
    have h2 : 1.4142 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ T ^ 2 := by positivity
    nlinarith
  -- Part a.
  have ha : K₀ / T ^ 3 * (U ^ 2 / q * (0.5004 * V ^ 2)) ≤ 0.1466 * (2 * T ^ 3 / t) := by
    have h1 : (U * V) ^ 2 ≤ (T ^ 3 / (2 * √t)) ^ 2 := pow_le_pow_left₀ (by positivity) hUV 2
    have h2 : (T ^ 3 / (2 * √t)) ^ 2 = T ^ 6 / (4 * t) := by
      rw [div_pow, mul_pow, Real.sq_sqrt ht0.le]; ring
    have e : K₀ / T ^ 3 * (U ^ 2 / q * (0.5004 * V ^ 2)) = K₀ * 0.5004 * (U * V) ^ 2 / (q * T ^ 3) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    calc K₀ * 0.5004 * (U * V) ^ 2 ≤ 2.3433 * 0.5004 * (T ^ 6 / (4 * t)) := by
          rw [← h2]; gcongr
      _ ≤ 0.1466 * (2 * T ^ 3 / t) * (q * T ^ 3) := by
          have e2 : 0.1466 * (2 * T ^ 3 / t) * (q * T ^ 3) = 0.2932 * q * (T ^ 6 / t) := by
            field_simp; norm_num
          have e3 : 2.3433 * 0.5004 * (T ^ 6 / (4 * t)) = 0.29314683 * (T ^ 6 / t) := by
            field_simp; ring
          rw [e2, e3]
          have : 0 < T ^ 6 / t := by positivity
          nlinarith
  -- Parts b, c.
  have hlog := log_le_sqrt_sharp hT
  have hlq : Real.log q ≤ Real.log T := Real.log_le_log hq0 (by linarith)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hb : K₀ / T ^ 3 * (U ^ 2 / q * (V * q * Real.log q)) ≤ 0.00042 * (T ^ 2 * √T) := by
    have e : K₀ / T ^ 3 * (U ^ 2 / q * (V * q * Real.log q)) = K₀ * U ^ 2 * V * Real.log q / T ^ 3 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have : U ^ 2 ≤ (0.0786 * T ^ 2) ^ 2 := pow_le_pow_left₀ hU0 hU2 2
    calc K₀ * U ^ 2 * V * Real.log q ≤ 2.3433 * (0.0786 * T ^ 2) ^ 2 * (9 * T / 2) * (0.0064 * √T) := by
          gcongr; linarith
      _ ≤ 0.00042 * (T ^ 2 * √T) * T ^ 3 := by
          have : 0 ≤ T ^ 5 * √T := by positivity
          nlinarith
  have hc : K₀ / T ^ 3 * ((2 * U + q) * (0.5004 * V ^ 2)) ≤ 0.00001 * (T ^ 2 * √T) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : V ^ 2 ≤ (9 * T / 2) ^ 2 := pow_le_pow_left₀ hV0 hV2 2
    calc K₀ * ((2 * U + q) * (0.5004 * V ^ 2)) ≤ 2.3433 * ((2 * (0.0786 * T ^ 2) + T) * (0.5004 * (9 * T / 2) ^ 2)) := by
          gcongr; linarith
      _ ≤ 0.00001 * (T ^ 2 * √T) * T ^ 3 := by
          have h1 : (0 : ℝ) ≤ T ^ 4 := by positivity
          have h2 : 2449 * T ^ 4 ≤ T ^ 4 * √T := by nlinarith
          nlinarith [pow_pos hT0 3, pow_pos hT0 4, pow_pos hT0 5]
  have e : K₀ / T ^ 3 * (U ^ 2 / q * (0.5004 * V ^ 2 + V * q * Real.log q) +
      (2 * U + q) * (0.5004 * V ^ 2)) = K₀ / T ^ 3 * (U ^ 2 / q * (0.5004 * V ^ 2)) +
      K₀ / T ^ 3 * (U ^ 2 / q * (V * q * Real.log q)) +
      K₀ / T ^ 3 * ((2 * U + q) * (0.5004 * V ^ 2)) := by ring
  have : 0 ≤ T ^ 2 * √T := by positivity
  rw [e]; linarith

/-- Common bounds on `c₊` and `√c₊` at the first parameters for `t ≥ 2`. -/
theorem cPlus_le_296 {T t : ℝ} (hT : 6e6 ≤ T) (ht2 : 2 ≤ t) :
    cPlus (T ^ 3) (U1 T t) (V1 T) ≤ 2.9606 := by
  have ht0 : 0 < t := by linarith
  have h := (cPlus_first hT ht0).2
  have : 1.4142 ≤ √t := by rw [Real.le_sqrt (by norm_num) ht0.le]; nlinarith
  have : 2.7726 / √t ≤ 2.7726 / 1.4142 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
  have : (2.7726 : ℝ) / 1.4142 ≤ 1.9606 := by norm_num
  linarith

theorem logPlus_le_log_of_le {y Y : ℝ} (hy : 0 < y) (hyY : y ≤ Y) (hY : 1 ≤ Y) :
    logPlus y ≤ Real.log Y :=
  max_le (Real.log_le_log hy hyY) (Real.log_nonneg hY)

set_option maxHeartbeats 1600000 in
/-- The rest of `S_{I,2}` for `|δ| ≤ 1/2c₂` ([B, (6.13)]) at the parameters:
`≤ 2.2 x/√t + 1.8105 · 2x/t + 0.0425 x^{5/6}`. -/
theorem typeI2_small_rest_first {T t : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : 1 ≤ q)
    (hqT : (q : ℝ) ≤ T / 6) (ht2 : 2 ≤ t) (htT : t ≤ T / 3) :
    1.0004 * coefUV (cPlus (T ^ 3) (U1 T t) (V1 T)) * ((U1 T t : ℝ) * V1 T) +
        1.0004 * coefQ (T ^ 3) q (U1 T t) (V1 T) (cPlus (T ^ 3) (U1 T t) (V1 T)) * (3 / 4 * T ^ 2) ≤
      2.2 * (T ^ 3 / √t) + 1.8105 * (2 * T ^ 3 / t) + 0.0425 * (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hst : 0 < √t := Real.sqrt_pos.2 ht0
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsT := sqrt_ge_2449 hT
  obtain ⟨hc1, hc2⟩ := cPlus_first hT ht0
  have hc3 := cPlus_le_296 hT ht2
  have hsc := sqrt_cPlus_first hT ht0
  set c := cPlus (T ^ 3) (U1 T t) (V1 T)
  obtain ⟨hc2a, hc2b⟩ := c₂_bounds
  obtain ⟨hc0a, hc0b⟩ := sqrt_c₀_bounds
  have hpi := Real.pi_gt_d6
  have he' := Real.exp_one_gt_d9
  have hUV := U1V1_le hT0 ht0
  have hUV0 : (0 : ℝ) ≤ (U1 T t : ℝ) * V1 T := by positivity
  -- `coefUV c ≤ 4.397837 + 7.23845/√t`.
  have hcoef : coefUV c ≤ 4.39786 + 7.2386 / √t := by
    unfold coefUV
    have h1 : √(c₀ * c) = √c₀ * √c := Real.sqrt_mul (by norm_num [c₀]) c
    rw [h1]
    have h2 : 2 * (√c₀ * √c) / π ≤ 3.57424 * (1 + 1.3863 / √t) := by
      rw [div_le_iff₀ (by linarith)]
      have hm : √c₀ * √c ≤ 5.6144 * (1 + 1.3863 / √t) :=
        mul_le_mul hc0b hsc (Real.sqrt_nonneg _) (by norm_num)
      have ha : 0 ≤ 1 + 1.3863 / √t := by positivity
      have : 3.57424 * (1 + 1.3863 / √t) * 3.141592 ≤ 3.57424 * (1 + 1.3863 / √t) * π :=
        mul_le_mul_of_nonneg_left hpi.le (by positivity)
      nlinarith
    have h3 : 3 * c / (2 * c₂ * rexp 1) ≤ 0.82362 * (1 + 2.7726 / √t) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 2 * 0.67 * 2.7182818283 ≤ 2 * c₂ * rexp 1 := by gcongr
      have ha : 0 ≤ 1 + 2.7726 / √t := by positivity
      have h2 : 0.82362 * (1 + 2.7726 / √t) * (2 * 0.67 * 2.7182818283) ≤
          0.82362 * (1 + 2.7726 / √t) * (2 * c₂ * rexp 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      nlinarith
    have e : 3.57424 * (1 + 1.3863 / √t) + 0.82362 * (1 + 2.7726 / √t) =
        4.39786 + (3.57424 * 1.3863 + 0.82362 * 2.7726) / √t := by ring
    have h4 : (3.57424 * 1.3863 + 0.82362 * 2.7726 : ℝ) ≤ 7.2386 := by norm_num
    have h5 : (3.57424 * 1.3863 + 0.82362 * 2.7726) / √t ≤ 7.2386 / √t :=
      div_le_div_of_nonneg_right h4 hst.le
    linarith
  have hB3 : 1.0004 * coefUV c * ((U1 T t : ℝ) * V1 T) ≤ 2.2 * (T ^ 3 / √t) + 1.8105 * (2 * T ^ 3 / t) := by
    have hcu0 : 0 ≤ coefUV c := coefUV_nonneg (by linarith)
    have hss : √t * √t = t := Real.mul_self_sqrt ht0.le
    calc 1.0004 * coefUV c * ((U1 T t : ℝ) * V1 T) ≤ 1.0004 * (4.39786 + 7.2386 / √t) * (T ^ 3 / (2 * √t)) := by
          gcongr
      _ = 1.0004 * 4.39786 / 2 * (T ^ 3 / √t) + 1.0004 * 7.2386 / 4 * (2 * T ^ 3 / (√t * √t)) := by
          field_simp; ring
      _ = 1.0004 * 4.39786 / 2 * (T ^ 3 / √t) + 1.0004 * 7.2386 / 4 * (2 * T ^ 3 / t) := by
          rw [hss]
      _ ≤ _ := by
          have : 0 ≤ T ^ 3 / √t := by positivity
          have : 0 ≤ 2 * T ^ 3 / t := by positivity
          gcongr <;> norm_num
  -- `coefQ ≤ 0.03936 √T + 41.6`.
  have hlog := log_le_sqrt_sharp hT
  have hU2 : (U1 T t : ℝ) ≤ 0.0786 * T ^ 2 := by
    refine (U1_le (T := T) ht0).trans ?_
    have h1 : √2 ≤ √t := Real.sqrt_le_sqrt ht2
    have h2 : 1.4142 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ T ^ 2 := by positivity
    nlinarith
  have hU := U1_ge hT ht0 htT
  have hU0 : (0 : ℝ) < U1 T t := lt_of_lt_of_le (by positivity) hU
  have hV2 := V1_le hT0
  have hV1 := V1_ge hT0
  have hη := eta2'L1_le
  have hη0 := eta2'L1_pos
  have hcQ : coefQ (T ^ 3) q (U1 T t) (V1 T) c ≤ 0.03937 * √T + 41.61 := by
    unfold coefQ
    have hs1 : √(c₀ * c) ≤ 9.661 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have : c₀ = 31.521 := rfl
      rw [this]; nlinarith
    have hs1' : √(c₀ * c) / π ≤ 3.0752 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hs10 : 0 ≤ √(c₀ * c) / π := by positivity
    have hlp : logPlus (2 * U1 T t / q) ≤ 0.0128 * √T := by
      have h1 : 2 * (U1 T t : ℝ) / q ≤ T ^ 2 := by
        rw [div_le_iff₀ hq0]; nlinarith
      refine (logPlus_le_log_of_le (by positivity) h1 (by nlinarith)).trans ?_
      rw [Real.log_pow]; push_cast; linarith
    have hel : 1 / rexp 1 ≤ 0.3679 := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
    have hmax : max 1 (Real.log (c₀ * rexp 3 * q ^ 2 * V1 T / (4 * π * eta2'L1 * T ^ 3))) = 1 := by
      refine max_eq_left ?_
      have he := Real.exp_one_lt_d9
      have he3 : rexp 3 ≤ 20.1 := by
        calc rexp 3 = rexp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
          _ ≤ 20.1 := by norm_num
      have hη5 : (5.5 : ℝ) ≤ eta2'L1 := by unfold eta2'L1; have := Real.log_two_gt_d9; linarith
      have harg : c₀ * rexp 3 * q ^ 2 * V1 T / (4 * π * eta2'L1 * T ^ 3) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have : (q : ℝ) ^ 2 ≤ T ^ 2 / 36 := by nlinarith
        have : c₀ * rexp 3 * q ^ 2 * V1 T ≤ 31.521 * 20.1 * (T ^ 2 / 36) * (9 * T / 2) := by
          have : c₀ = 31.521 := rfl
          rw [this]; gcongr
        have : 2 * (4 * 3.141592 * 5.5 * T ^ 3) ≤ 2 * (4 * π * eta2'L1 * T ^ 3) := by gcongr
        nlinarith [pow_pos hT0 3]
      have := Real.log_le_sub_one_of_pos (show 0 < c₀ * rexp 3 * q ^ 2 * V1 T / (4 * π * eta2'L1 * T ^ 3) by
        have : (0 : ℝ) < c₀ := by norm_num [c₀]
        have : (0 : ℝ) < V1 T := by linarith
        positivity)
      linarith
    rw [hmax]
    have h3 : 2 * √(3 * c₀ * c) / π ≤ 10.653 := by
      rw [div_le_iff₀ (by linarith)]
      have : √(3 * c₀ * c) ≤ 16.733 := by
        rw [Real.sqrt_le_left (by norm_num)]
        have : c₀ = 31.521 := rfl
        rw [this]; nlinarith
      nlinarith
    have h4 : 3 * c / (2 * c₂) ≤ 6.629 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    have h5 : 55 * c₀ * c₂ / (6 * π ^ 2) ≤ 19.66 := by
      rw [c₂_identity', div_le_iff₀ (by linarith)]; nlinarith
    have h6 : 2 * eta2'L1 / π ≤ 3.5304 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have : √(c₀ * c) / π * (logPlus (2 * U1 T t / q) + 1 / rexp 1) ≤ 3.0752 * (0.0128 * √T + 0.3679) := by
      have : 0 ≤ logPlus (2 * U1 T t / q) := logPlus_nonneg _
      gcongr
    nlinarith
  have hB4 : 1.0004 * coefQ (T ^ 3) q (U1 T t) (V1 T) c * (3 / 4 * T ^ 2) ≤ 0.0425 * (T ^ 2 * √T) := by
    have h0 : 0 ≤ coefQ (T ^ 3) q (U1 T t) (V1 T) c := coefQ_nonneg _ _ _ _ (by linarith)
    calc 1.0004 * coefQ (T ^ 3) q (U1 T t) (V1 T) c * (3 / 4 * T ^ 2)
        ≤ 1.0004 * (0.03937 * √T + 41.61) * (3 / 4 * T ^ 2) := by gcongr
      _ ≤ 0.0425 * (T ^ 2 * √T) := by
          have : 2449 * T ^ 2 ≤ T ^ 2 * √T := by nlinarith [pow_pos hT0 2]
          nlinarith [pow_pos hT0 2]
  linarith

end TernaryGoldbach.MinorArcs
