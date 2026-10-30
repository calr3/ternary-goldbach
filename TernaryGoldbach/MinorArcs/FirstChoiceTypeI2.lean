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

theorem logPlus_le_log_of_le' {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) (hY : 1 ≤ Y) :
    logPlus y ≤ Real.log Y := by
  rcases hy.lt_or_eq with h | h
  · exact logPlus_le_log_of_le h hyY hY
  · rw [← h]; simp [logPlus]; exact Real.log_nonneg hY

/-- `(A + log⁺(cy))/y ≤ (A + log⁺(cy₀))/y₀` for `y ≥ y₀ > 0`, `A ≥ 1`, `c > 0`. -/
theorem div_logPlus_anti {A c y y₀ : ℝ} (hA : 1 ≤ A) (hc : 0 < c) (hy₀ : 0 < y₀) (hy : y₀ ≤ y) :
    (A + logPlus (c * y)) / y ≤ (A + logPlus (c * y₀)) / y₀ := by
  have hy0 : 0 < y := lt_of_lt_of_le hy₀ hy
  have h1 : logPlus (c * y) ≤ logPlus (c * y₀) + (y / y₀ - 1) := by
    have hl := Real.log_le_sub_one_of_pos (show 0 < y / y₀ by positivity)
    have hl0 : 0 ≤ Real.log (y / y₀) := Real.log_nonneg (by rw [le_div_iff₀ hy₀]; linarith)
    unfold logPlus
    refine max_le ?_ ?_
    · have : Real.log (c * y) = Real.log (c * y₀) + Real.log (y / y₀) := by
        rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
      rw [this]
      have := le_max_left (Real.log (c * y₀)) 0
      linarith
    · have := le_max_right (Real.log (c * y₀)) 0
      linarith
  have hB : 1 ≤ A + logPlus (c * y₀) := by have := logPlus_nonneg (c * y₀); linarith
  rw [div_le_div_iff₀ hy0 hy₀]
  have hr : 0 ≤ y / y₀ - 1 := by rw [sub_nonneg, le_div_iff₀ hy₀]; linarith
  have e : y = y₀ * (y / y₀) := by field_simp
  have : (A + logPlus (c * y₀) - 1) * (y / y₀ - 1) ≥ 0 := mul_nonneg (by linarith) hr
  calc (A + logPlus (c * y)) * y₀ ≤ (A + logPlus (c * y₀) + (y / y₀ - 1)) * y₀ :=
        mul_le_mul_of_nonneg_right (by linarith) hy₀.le
    _ ≤ (A + logPlus (c * y₀)) * (y₀ * (y / y₀)) := by nlinarith
    _ = (A + logPlus (c * y₀)) * y := by rw [← e]

theorem logPlus_mono' {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : logPlus a ≤ logPlus b := by
  rcases ha.lt_or_eq with h | h
  · exact max_le_max (Real.log_le_log h hab) le_rfl
  · rw [← h]; simp only [logPlus, Real.log_zero, max_self]; exact logPlus_nonneg b

/-- The `x/|δ|q` part of (6.14) at the parameters: `≤ (2.016 log t + 0.3108) · 2x/t`. -/
theorem typeI2_B8x_first {x δ U V : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : 0 < x)
    (hδ : 1 / (2 * c₂) ≤ |δ|) (hUV0 : 0 ≤ U * V)
    (hUV : U * V ≤ x / (2 * √(delta0 δ * q))) :
    x / (|δ| * q) * (1.03883 + Real.log q + logPlus (6 * U * V * |δ| * q / (√2 * x))) ≤
      (2.016 * Real.log (delta0 δ * q) + 0.3108) * (2 * x / (delta0 δ * q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hc2a, hc2b⟩ := c₂_bounds
  have hc2p := c₂_pos
  have hδ0 : 0 < |δ| := lt_of_lt_of_le (by positivity) hδ
  have hd := delta0_ge δ
  set t := delta0 δ * q with ht
  have ht2 : 2 ≤ t := by rw [ht]; nlinarith
  have ht0 : 0 < t := by linarith
  have hst : 0 < √t := Real.sqrt_pos.2 ht0
  have hs2 : 0 < √2 := by positivity
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have harg : 6 * U * V * |δ| * q / (√2 * x) ≤ 3 * |δ| * q / (√2 * √t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : U * V * (2 * √t) ≤ x := by rwa [le_div_iff₀ (by positivity)] at hUV
    have : 0 ≤ |δ| * q * √2 := by positivity
    nlinarith
  have harg0 : 0 ≤ 6 * U * V * |δ| * q / (√2 * x) := by
    rw [show 6 * U * V * |δ| * q = 6 * (U * V) * |δ| * q by ring]; positivity
  have hlogq : Real.log q ≤ Real.log t - 0.693147 := by
    have h1 : Real.log q ≤ Real.log (t / 2) := Real.log_le_log hq0 (by rw [ht]; nlinarith)
    rw [Real.log_div ht0.ne' (by norm_num)] at h1; linarith
  rcases le_or_gt (|δ| / 4) 2 with h8 | h8
  · -- `δ₀ = 2`, `t = 2q`.
    have hd0 : delta0 δ = 2 := by unfold delta0; exact max_eq_left h8
    have htq : t = 2 * q := by rw [ht, hd0]
    have hsq0 : 0 < √q := Real.sqrt_pos.2 hq0
    have hsq : √2 * √t = 2 * √q := by
      rw [htq, ← Real.sqrt_mul (by norm_num), show (2 : ℝ) * (2 * q) = 2 ^ 2 * q by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have harg2 : 6 * U * V * |δ| * q / (√2 * x) ≤ 1.5 * √q * |δ| := by
      refine harg.trans (le_of_eq ?_)
      rw [hsq, show 3 * |δ| * q / (2 * √q) = 1.5 * |δ| * (q / √q) by ring, Real.div_sqrt]
      ring
    have hlp := logPlus_mono' harg0 harg2
    set A := 1.03883 + Real.log q with hA
    have hA1 : 1 ≤ A := by rw [hA]; linarith
    have hmono := div_logPlus_anti hA1 (show 0 < 1.5 * √q by positivity)
      (show 0 < 1 / (2 * c₂) by positivity) hδ
    -- `log⁺(1.5√q/(2c₂)) ≤ 0.11941 + log q/2`.
    have hlp2 : logPlus (1.5 * √q * (1 / (2 * c₂))) ≤ 0.11941 + Real.log q / 2 := by
      have h1 : 1.5 * √q * (1 / (2 * c₂)) ≤ 1.11941 * √q := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith
      have h2 : 1 ≤ 1.11941 * √q := by
        have : 1 ≤ √q := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hq1
        nlinarith
      refine (logPlus_le_log_of_le' (by positivity) h1 h2).trans ?_
      rw [Real.log_mul (by norm_num) hsq0.ne', Real.log_sqrt hq0.le]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.11941 by norm_num)
      linarith
    calc x / (|δ| * q) * (A + logPlus (6 * U * V * |δ| * q / (√2 * x)))
        ≤ x / (|δ| * q) * (A + logPlus (1.5 * √q * |δ|)) := by gcongr
      _ = x / q * ((A + logPlus (1.5 * √q * |δ|)) / |δ|) := by field_simp
      _ ≤ x / q * ((A + logPlus (1.5 * √q * (1 / (2 * c₂)))) / (1 / (2 * c₂))) := by gcongr
      _ = x / q * (2 * c₂ * (A + logPlus (1.5 * √q * (1 / (2 * c₂))))) := by field_simp
      _ ≤ x / q * (1.344 * (A + (0.11941 + Real.log q / 2))) := by
          have : 0 ≤ A + logPlus (1.5 * √q * (1 / (2 * c₂))) := by
            have := logPlus_nonneg (1.5 * √q * (1 / (2 * c₂))); linarith
          gcongr
          · linarith
      _ ≤ (2.016 * Real.log t + 0.3108) * (2 * x / t) := by
          have hin : 1.344 * (A + (0.11941 + Real.log q / 2)) ≤ 2.016 * Real.log t + 0.3108 := by
            rw [hA]; linarith
          have e : 2 * x / t = x / q := by rw [htq]; field_simp
          rw [e, mul_comm (2.016 * Real.log t + 0.3108)]
          exact mul_le_mul_of_nonneg_left hin (by positivity)
  · -- `δ₀ = |δ|/4`.
    have hd0 : delta0 δ = |δ| / 4 := by unfold delta0; exact max_eq_right h8.le
    have hδt : |δ| * q = 4 * t := by rw [ht, hd0]; ring
    have harg2 : 6 * U * V * |δ| * q / (√2 * x) ≤ 8.4854 * √t := by
      refine harg.trans ?_
      rw [show 3 * |δ| * q = 3 * (|δ| * q) by ring, hδt, div_le_iff₀ (by positivity)]
      have : √t * √t = t := Real.mul_self_sqrt ht0.le
      have : 1.41421 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      nlinarith
    have hlp : logPlus (6 * U * V * |δ| * q / (√2 * x)) ≤ 2.1402 + Real.log t / 2 := by
      have h1 : 1 ≤ 8.4854 * √t := by
        have : 1.4142 ≤ √t := by rw [Real.le_sqrt (by norm_num) ht0.le]; nlinarith
        nlinarith
      refine (logPlus_le_log_of_le' harg0 harg2 h1).trans ?_
      rw [Real.log_mul (by norm_num) hst.ne', Real.log_sqrt ht0.le]
      have h8 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8.4854 / 8 by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
        Real.log_pow] at h8
      push_cast at h8
      linarith
    rw [hδt]
    have e : x / (4 * t) = (2 * x / t) / 8 := by field_simp; ring
    rw [e]
    have : 0 ≤ 2 * x / t := by positivity
    have hG : 1.03883 + Real.log q + logPlus (6 * U * V * |δ| * q / (√2 * x)) ≤
        1.5 * Real.log t + 2.4859 := by linarith
    calc 2 * x / t / 8 * (1.03883 + Real.log q + logPlus (6 * U * V * |δ| * q / (√2 * x)))
        ≤ 2 * x / t / 8 * (1.5 * Real.log t + 2.4859) := by gcongr
      _ ≤ _ := by
          rw [mul_comm ((2.016 * Real.log t + 0.3108))]
          have e2 : 2 * x / t / 8 * (1.5 * Real.log t + 2.4859) =
              2 * x / t * ((1.5 * Real.log t + 2.4859) / 8) := by ring
          rw [e2]
          gcongr
          linarith

end TernaryGoldbach.MinorArcs
