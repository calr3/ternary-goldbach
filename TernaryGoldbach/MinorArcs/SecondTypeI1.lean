import TernaryGoldbach.MinorArcs.SecondTypeIIb
import TernaryGoldbach.MinorArcs.FirstChoiceTypeI2b

/-!
# Type I at the second parameters [B, §6.3.2]: `S_{I,1}` and (4.50)

The cases are those of `second_case_split`: (a) `q > T/6`, or (b) `q ≤ T/6`, `|δ| > 8`,
`|δ|q > 8T/6`. In both cases `x/(2q) · 2/δ₀ ≤ 3T²` and `q/φ(q) ≤ 1.7882 log(2L) + 0.9549`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2)

/-- The case hypothesis of the second choice. -/
def SecondCase (T δ : ℝ) (q : ℕ) : Prop :=
  T / 6 < q ∨ ((q : ℝ) ≤ T / 6 ∧ 8 < |δ| ∧ 8 * (T / 6) < |δ| * q)

theorem xq_delta0_le {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hc : SecondCase T δ q) :
    T ^ 3 / (2 * q) * (2 / delta0 δ) ≤ 3 * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast h.1
  have hd := delta0_ge δ
  rcases hc with hc | ⟨-, hδ8, hδq⟩
  · have h1 : 2 / delta0 δ ≤ 1 := by rw [div_le_one (by linarith)]; exact hd
    have h2 : T ^ 3 / (2 * q) ≤ 3 * T ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [pow_pos hT0 2]
    calc T ^ 3 / (2 * q) * (2 / delta0 δ) ≤ 3 * T ^ 2 * 1 :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = _ := by ring
  · have hδ0 : delta0 δ = |δ| / 4 := by unfold delta0; rw [max_eq_right]; linarith
    rw [hδ0]
    have hδp : 0 < |δ| := by linarith
    have e : T ^ 3 / (2 * q) * (2 / (|δ| / 4)) = 4 * T ^ 3 / (|δ| * q) := by field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [pow_pos hT0 2]

theorem q_totient_le_F2 {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hc : SecondCase T δ q) :
    (q : ℝ) / Nat.totient q ≤ 1.7882 * Real.log (2 * Real.log T) + 0.9549 := by
  have hT0 : 0 < T := by linarith
  have hL := fifteen_six_le_log hT
  have hq1 := h.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  rcases hc with hc | ⟨hc, -, -⟩
  · have hF := div_totient_le_large (q := q) (by linarith)
    have hQT : Q2 T ≤ T ^ 2 := by
      unfold Q2; rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]
    have hqT : (q : ℝ) ≤ T ^ 2 := h.2.2.2.2.trans hQT
    have hlq : Real.log q ≤ 2 * Real.log T := by
      have := Real.log_le_log hq0 hqT
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hlq1 : 0 < Real.log q := Real.log_pos (by linarith)
    have := Real.log_le_log hlq1 hlq
    linarith
  · have hF := div_totient_le_F0 hq1 hT hc
    unfold a1F0 at hF
    have := Real.log_le_log (by linarith) (show Real.log T - 1.7917 ≤ 2 * Real.log T by linarith)
    linarith

/-- `log y ≤ y/e`. -/
theorem log_le_div_e {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / rexp 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < y / rexp 1 by positivity)
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

theorem logPlus_div_le {z : ℝ} (hz : 0 < z) : logPlus z / z ≤ 0.368 := by
  unfold logPlus
  rcases le_total (Real.log z) 0 with h | h
  · rw [max_eq_right h]; simp only [zero_div]; norm_num
  · rw [max_eq_left h, div_le_iff₀ hz]
    have := log_le_div_e hz
    have he := Real.exp_one_gt_d9
    have : z / rexp 1 ≤ 0.368 * z := by rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
    linarith

set_option maxHeartbeats 4000000 in
/-- (4.41) at the second parameters (`U = ⌊1225T⌋`, `q ≤ Q₀ = T²/349`). -/
theorem b441_second {T : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ T ^ 2 / 349) :
    bound_4_41 (T ^ 3) q (U2 T) ≤
      (0.0406 * Real.log T ^ 2 + 0.1408 * Real.log T + 0.0154) * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hsT := sqrt_ge_2449 hT
  have hss : √T * √T = T := Real.mul_self_sqrt hT0.le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hU := U2_le hT0
  have hU' := U2_ge' hT
  set U := (U2 T : ℝ)
  have hU0 : 0 < U := by linarith
  obtain ⟨hc2a, hc2b⟩ := c₂_bounds
  obtain ⟨hc0a, hc0b⟩ := sqrt_c₀_bounds
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  have hη := eta2'L1_le
  have hη0 := eta2'L1_pos
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  unfold bound_4_41
  simp only []
  -- `c₁ ≤ 1.000001`.
  set c₁ := 1 + eta2'L1 / (T ^ 3 / U) with hc₁
  have hc1 : 1 ≤ c₁ := by
    have : 0 ≤ eta2'L1 / (T ^ 3 / U) := by positivity
    linarith
  have hc1' : c₁ ≤ 1.000001 := by
    have : eta2'L1 / (T ^ 3 / U) ≤ 1e-6 := by
      rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
      have : U * eta2'L1 ≤ 1225 * T * 5.5452 := mul_le_mul hU hη hη0.le (by positivity)
      have : T ^ 3 = T * T ^ 2 := by ring
      nlinarith [pow_pos hT0 2]
    linarith
  have hsq1 : √(c₀ * c₁) ≤ 5.6145 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have : c₀ = √c₀ ^ 2 := (Real.sq_sqrt (by norm_num [c₀])).symm
    have : √c₀ ^ 2 ≤ 5.6144 ^ 2 := pow_le_pow_left₀ (by linarith) hc0b 2
    have hc00 : (0 : ℝ) < c₀ := by norm_num [c₀]
    nlinarith
  have hA : 2 * √(c₀ * c₁) / π ≤ 3.5745 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hA0 : 0 ≤ 2 * √(c₀ * c₁) / π := by positivity
  have hLT : 1225 * T * L ≤ 0.000205 * L * T ^ 2 := by
    have : 1225 * T ≤ 0.000205 * T ^ 2 := by nlinarith
    nlinarith
  -- Term a.
  have ta : 2 * √(c₀ * c₁) / π * U * Real.log (rexp 1 * T ^ 3 / U) ≤ 0.00146 * L * T ^ 2 := by
    have hl : Real.log (rexp 1 * T ^ 3 / U) ≤ 2 * L := by
      have h1 : rexp 1 * T ^ 3 / U ≤ T ^ 2 := by
        rw [div_le_iff₀ hU0]
        have : T ^ 3 = T * T ^ 2 := by ring
        have := mul_le_mul_of_nonneg_left hU' (sq_nonneg T)
        nlinarith [pow_pos hT0 3]
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hl0 : 0 ≤ Real.log (rexp 1 * T ^ 3 / U) := Real.log_nonneg (by
      rw [le_div_iff₀ hU0, one_mul]
      have h1 : 1225 * T ≤ T ^ 3 := by
        have : T ^ 3 = T * T ^ 2 := by ring
        rw [this]; nlinarith [pow_pos hT0 2]
      nlinarith [pow_pos hT0 3])
    calc 2 * √(c₀ * c₁) / π * U * Real.log (rexp 1 * T ^ 3 / U)
        ≤ 3.5745 * (1225 * T) * (2 * L) := by gcongr
      _ ≤ 0.00146 * L * T ^ 2 := by nlinarith
  -- Term b, via `logPlus z / z ≤ 0.368`.
  have tb : 3 * c₁ / 2 * (T ^ 3 / q) * logPlus (U / (c₂ * T ^ 3 / q)) * Real.log (q / c₂) ≤
      0.00034 * L * T ^ 2 := by
    set z := U / (c₂ * T ^ 3 / q)
    have hz : 0 < z := by positivity
    have e : T ^ 3 / q = U / c₂ / z := by simp only [z]; field_simp
    have hlq : Real.log (q / c₂) ≤ 2 * L := by
      have h1 : (q : ℝ) / c₂ ≤ T ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        have : (q : ℝ) * 349 ≤ T ^ 2 := by rwa [le_div_iff₀ (by norm_num)] at hqQ
        nlinarith [sq_nonneg T]
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hlq0 : 0 ≤ Real.log (q / c₂) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hlz := logPlus_div_le hz
    have hlz0 : 0 ≤ logPlus z := logPlus_nonneg _
    rw [e]
    calc 3 * c₁ / 2 * (U / c₂ / z) * logPlus z * Real.log (q / c₂)
        = 3 * c₁ / 2 * (U / c₂) * (logPlus z / z) * Real.log (q / c₂) := by field_simp
      _ ≤ 3 * 1.000001 / 2 * (1225 * T / 0.67) * 0.368 * (2 * L) := by
          gcongr
      _ ≤ 0.00034 * L * T ^ 2 := by
          have h1 : 1225 * T / 0.67 ≤ 1828.4 * T := by rw [div_le_iff₀ (by norm_num)]; nlinarith
          have h2 : 2018.6 * T ≤ 0.00034 * T ^ 2 := by nlinarith
          have hL0 : 0 ≤ L := by linarith
          nlinarith [mul_le_mul_of_nonneg_right h1 hL0, mul_le_mul_of_nonneg_right h2 hL0]
  -- Term c.
  have tc : (2 * eta2'L1 / π * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3))) *
      Real.log (T ^ 3) + 2 * √(c₀ * c₁) / π * (√3 + 1 / 2 * logPlus (U / (q / 2))) *
        Real.log (q / c₂)) * q ≤ (0.04059 * L ^ 2 + 0.11542 * L) * T ^ 2 := by
    have hmax : max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3))) ≤ L := by
      refine max_le (by linarith) ?_
      have he3 : rexp 3 ≤ 20.1 := by
        calc rexp 3 = rexp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
          _ ≤ 20.1 := by norm_num
      have harg : c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3) ≤ T := by
        rw [div_le_iff₀ (by positivity)]
        have hq2 : (q : ℝ) ^ 2 ≤ T ^ 4 / 121801 := by
          have : (q : ℝ) * 349 ≤ T ^ 2 := by rwa [le_div_iff₀ (by norm_num)] at hqQ
          rw [le_div_iff₀ (by norm_num)]; nlinarith
        have : c₀ * rexp 3 * q ^ 2 ≤ 31.521 * 20.1 * (T ^ 4 / 121801) := by
          have : c₀ = 31.521 := rfl
          rw [this]; gcongr
        have : (5.5 : ℝ) ≤ eta2'L1 := by unfold eta2'L1; have := Real.log_two_gt_d9; linarith
        have : T * (4 * π * eta2'L1 * T ^ 3) ≥ T * (4 * 3.1415 * 5.5 * T ^ 3) := by gcongr
        nlinarith [pow_pos hT0 4]
      have hpos : 0 < c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3) := by
        have : (0 : ℝ) < c₀ := by norm_num [c₀]
        positivity
      exact Real.log_le_log hpos harg
    have hlx : Real.log (T ^ 3) = 3 * L := by rw [Real.log_pow]; push_cast; ring
    have hlp : logPlus (U / (q / 2)) ≤ L + 7.8039 := by
      unfold logPlus
      refine max_le ?_ (by linarith)
      have h1 : U / (q / 2) ≤ 2450 * T := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have h2 : Real.log (2450 * T) ≤ L + 7.8039 := by
        rw [Real.log_mul (by norm_num) hT0.ne']
        have := log_le_num (z := 2450) 7 0.8039 (by norm_num) (by norm_num) (by norm_num [taylor6])
        norm_num at this ⊢; linarith
      exact (Real.log_le_log (by positivity) h1).trans h2
    have hlq : Real.log (q / c₂) ≤ 2 * L := by
      have h1 : (q : ℝ) / c₂ ≤ T ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        have : (q : ℝ) * 349 ≤ T ^ 2 := by rwa [le_div_iff₀ (by norm_num)] at hqQ
        nlinarith [sq_nonneg T]
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hlq0 : 0 ≤ Real.log (q / c₂) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hη' : 2 * eta2'L1 / π ≤ 3.5304 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hη0' : 0 ≤ 2 * eta2'L1 / π := by positivity
    have hs3 : √3 ≤ 1.7321 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hm0 : 0 ≤ max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3))) :=
      le_trans zero_le_one (le_max_left _ _)
    rw [hlx]
    calc (2 * eta2'L1 / π * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3))) *
          (3 * L) + 2 * √(c₀ * c₁) / π * (√3 + 1 / 2 * logPlus (U / (q / 2))) *
            Real.log (q / c₂)) * q
        ≤ (3.5304 * L * (3 * L) + 3.5745 * (1.7321 + 1 / 2 * (L + 7.8039)) * (2 * L)) *
            (T ^ 2 / 349) := by
          have : 0 ≤ logPlus (U / (q / 2)) := logPlus_nonneg _
          gcongr
      _ ≤ _ := by nlinarith [sq_nonneg T, sq_nonneg L]
  -- Terms d, e.
  have hlx2 : Real.log (2 * T ^ 3 / c₂) ≤ 3 * L + 1.094 := by
    have h1 : 2 * T ^ 3 / c₂ ≤ 2.9851 * T ^ 3 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hT0 3]
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    have h2 := log_le_num (z := 2.9851) 1 0.094 (by norm_num) (by norm_num) (by norm_num [taylor6])
    norm_num at h2; push_cast at this; linarith
  have hsx : √(2 * T ^ 3 / c₂) ≤ 1.7278 * (T * √T) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, sq (√T), hss, div_le_iff₀ (by linarith)]
    nlinarith [pow_pos hT0 3]
  have td : 3 * c₁ / 2 * √(2 * T ^ 3 / c₂) * Real.log (2 * T ^ 3 / c₂) ≤
      (0.003175 * L + 0.001158) * T ^ 2 := by
    have hl0 : 0 ≤ Real.log (2 * T ^ 3 / c₂) := Real.log_nonneg (by
      rw [le_div_iff₀ (by linarith)]; nlinarith [pow_pos hT0 3])
    calc 3 * c₁ / 2 * √(2 * T ^ 3 / c₂) * Real.log (2 * T ^ 3 / c₂)
        ≤ 3 * 1.000001 / 2 * (1.7278 * (T * √T)) * (3 * L + 1.094) := by gcongr
      _ ≤ _ := by
          have : T * √T * 2449 ≤ T ^ 2 := by nlinarith
          nlinarith
  have hc232 : c₂ ^ (3 / 2 : ℝ) ≤ 0.5509 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have : √c₂ ≤ 0.81976 := by rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    nlinarith [Real.sqrt_nonneg c₂]
  have hlx3 : Real.log (2 * rexp 1 * T ^ 3 / c₂) ≤ 3 * L + 2.094 := by
    have h1 : 2 * rexp 1 * T ^ 3 / c₂ ≤ 8.1145 * T ^ 3 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hT0 3]
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    have h2 := log_le_num (z := 8.1145) 2 0.094 (by norm_num) (by norm_num) (by norm_num [taylor6])
    norm_num at h2; push_cast at this; linarith
  have te : 20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) * √(2 * T ^ 3) * Real.log (2 * rexp 1 * T ^ 3 / c₂) ≤
      (0.0204 * L + 0.0142) * T ^ 2 := by
    have hl0 : 0 ≤ Real.log (2 * rexp 1 * T ^ 3 / c₂) := Real.log_nonneg (by
      rw [le_div_iff₀ (by linarith)]; nlinarith [pow_pos hT0 3])
    have hsx2 : √(2 * T ^ 3) ≤ 1.41422 * (T * √T) := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, sq (√T), hss]; nlinarith [pow_pos hT0 3]
    have hk : 20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) ≤ 11.74 := by
      have : c₀ = 31.521 := rfl
      rw [this, div_le_iff₀ (by positivity)]
      have : 0 ≤ c₂ ^ (3 / 2 : ℝ) := by positivity
      nlinarith
    have hk0 : 0 ≤ 20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) := by
      have : (0 : ℝ) < c₀ := by norm_num [c₀]
      positivity
    calc 20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) * √(2 * T ^ 3) * Real.log (2 * rexp 1 * T ^ 3 / c₂)
        ≤ 11.74 * (1.41422 * (T * √T)) * (3 * L + 2.094) := by gcongr
      _ ≤ _ := by
          have : T * √T * 2449 ≤ T ^ 2 := by nlinarith
          nlinarith
  have hL0 : 0 ≤ L := by linarith
  linarith [mul_nonneg (sq_nonneg L) (sq_nonneg T), mul_nonneg hL0 (sq_nonneg T), sq_nonneg T]

/-- `log(Vq)/q ≤ log(Vq₀)/q₀` for `q₀ ≤ q`, `Vq₀ ≥ e`. -/
theorem log_mul_div_anti {V q₀ q : ℝ} (hV : 0 < V) (hq₀ : 0 < q₀) (hq : q₀ ≤ q)
    (he : rexp 1 ≤ V * q₀) : Real.log (V * q) / q ≤ Real.log (V * q₀) / q₀ := by
  have h := Real.log_div_self_antitoneOn (Set.mem_Ici.2 he)
    (Set.mem_Ici.2 (he.trans (mul_le_mul_of_nonneg_left hq hV.le)))
    (mul_le_mul_of_nonneg_left hq hV.le)
  simp only at h
  have hq0 : 0 < q := by linarith
  have e1 : Real.log (V * q) / q = V * (Real.log (V * q) / (V * q)) := by field_simp
  have e2 : Real.log (V * q₀) / q₀ = V * (Real.log (V * q₀) / (V * q₀)) := by field_simp
  rw [e1, e2]; exact mul_le_mul_of_nonneg_left h hV.le

theorem minInv_nonneg' (δ : ℝ) : 0 ≤ minInv c₀ (π * δ) := by
  unfold minInv; split_ifs
  · norm_num
  · exact le_min zero_le_one (div_nonneg (by norm_num [c₀]) (sq_nonneg _))

theorem logFB_nonneg (δ : ℝ) : 0 ≤ logFourierBound δ := by
  have hl4 : 0 ≤ 2 - Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; linarith
  unfold logFourierBound; split_ifs
  · exact hl4
  · exact le_min hl4 (by positivity)

set_option maxHeartbeats 4000000 in
/-- **`S_{I,1}` at the second parameters**: `≤ (0.0406 L² + 14.1 L + 15.7) T²`. -/
theorem typeI1_second {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hc : SecondCase T δ q) :
    ‖typeILog α (T ^ 3) (U2 T)‖ ≤
      (0.0406 * Real.log T ^ 2 + 14.1 * Real.log T + 15.7) * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hq1 := h.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hU := U2_le hT0
  have hU' := U2_ge' hT
  have hU0 := U2_pos hT
  have hqQ : (q : ℝ) ≤ T ^ 2 / 349 := h.2.2.2.2
  have key := typeI1_le h (U := U2 T) (by
      have : √3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      linarith)
    (le_min (by nlinarith) (by
      rw [le_div_iff₀ (Real.exp_pos 1)]
      have := Real.exp_one_lt_d9
      have : 1225 * T * 3 ≤ T ^ 3 := by
        have : T ^ 3 = T * T ^ 2 := by ring
        rw [this]; nlinarith [pow_pos hT0 2]
      nlinarith))
    (U2_le_Q2 hT)
  refine key.trans ?_
  have hxm : T ^ 3 / (2 * q) * minInv c₀ (π * δ) ≤ 3 * T ^ 2 :=
    (mul_le_mul_of_nonneg_left (minInv_le_delta0 δ) (by positivity)).trans (xq_delta0_le hT h hc)
  have hxm0 : 0 ≤ T ^ 3 / (2 * q) * minInv c₀ (π * δ) :=
    mul_nonneg (by positivity) (minInv_nonneg' δ)
  -- the bracket.
  have hF := q_totient_le_F2 hT h hc
  have hl2L : Real.log (2 * L) ≤ 0.7358 * L := by
    have := log_le_div_e (show 0 < 2 * L by linarith)
    have he := Real.exp_one_gt_d9
    have : 2 * L / rexp 1 ≤ 0.7358 * L := by rw [div_le_iff₀ (Real.exp_pos 1)]; nlinarith
    linarith
  have hφ2 : (2 * q : ℝ) / Nat.totient (2 * q) ≤ 2 * ((q : ℝ) / Nat.totient q) := by
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 hq1
    have h1 : (Nat.totient q : ℝ) ≤ Nat.totient (2 * q) := by
      exact_mod_cast totient_le_totient_two_mul q
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hq0.le hφ h1) (by norm_num)
  have hlxU : Real.log (T ^ 3 / U2 T) ≤ 2 * L := by
    have := Real.log_le_log (by positivity) ((xU2_le hT).trans (show T ^ 2 / 1224.99 ≤ T ^ 2 by
      rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]))
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlxU0 : 0 ≤ Real.log (T ^ 3 / U2 T) := Real.log_nonneg (by
    rw [le_div_iff₀ hU0, one_mul]
    have : T ^ 3 = T * T ^ 2 := by ring
    rw [this]; nlinarith [pow_pos hT0 2])
  have hmu := muBound_le_one (U2 T) q
  have hmu0 := muBound_nonneg (U2 T) hq1
  have hbr : (2 * (q : ℝ) / (Nat.totient (2 * q) : ℝ) + 2.67) +
      Real.log (T ^ 3 / U2 T) * muBound (U2 T) q ≤ 4.6396 * L + 4.58 := by
    have h1 : Real.log (T ^ 3 / U2 T) * muBound (U2 T) q ≤ 2 * L := by
      nlinarith [mul_le_mul hlxU hmu hmu0 (by linarith)]
    have h2 : 2 * (q : ℝ) / (Nat.totient (2 * q) : ℝ) ≤ 2 * (1.7882 * (0.7358 * L) + 0.9549) := by
      nlinarith
    nlinarith
  have hbr0 : 0 ≤ (2 * (q : ℝ) / (Nat.totient (2 * q) : ℝ) + 2.67) +
      Real.log (T ^ 3 / U2 T) * muBound (U2 T) q := by positivity
  have tA := mul_le_mul hxm hbr hbr0 (by positivity)
  -- `logFB`.
  have tB : T ^ 3 / (2 * q) * logFourierBound δ * muBound (U2 T) q ≤ 1.8414 * T ^ 2 := by
    have h1 : T ^ 3 / (2 * q) * logFourierBound δ ≤ 0.6138 * (3 * T ^ 2) := by
      have := mul_le_mul_of_nonneg_left (logFB_le_delta0 δ) (show 0 ≤ T ^ 3 / (2 * q) by positivity)
      have h2 := xq_delta0_le hT h hc
      nlinarith
    have h0 : 0 ≤ T ^ 3 / (2 * q) * logFourierBound δ := mul_nonneg (by positivity) (logFB_nonneg δ)
    nlinarith [mul_le_mul h1 hmu hmu0 (by positivity)]
  -- the `c₀(1/2 - 2/π²)` term.
  have tC : c₀ * (1 / 2 - 2 / π ^ 2) * ((U2 T : ℝ) ^ 2 / (4 * q * T ^ 3) *
      Real.log (rexp (1 / 2) * T ^ 3 / U2 T) + 1 / rexp 1) ≤ 0.001 * L * T ^ 2 := by
    have hk : c₀ * (1 / 2 - 2 / π ^ 2) ≤ 15.761 := by
      have h0 : 0 ≤ 2 / π ^ 2 := by positivity
      have hc : c₀ = 31.521 := rfl
      rw [hc]; nlinarith
    have hk0 : 0 ≤ c₀ * (1 / 2 - 2 / π ^ 2) :=
      mul_nonneg (by norm_num [c₀]) (by linarith [pi_two_div_sq_le])
    have h1 : (U2 T : ℝ) ^ 2 / (4 * q * T ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h0 : (U2 T : ℝ) ^ 2 ≤ (1225 * T) ^ 2 := pow_le_pow_left₀ hU0.le hU 2
      have h3 : T ^ 3 = T * T ^ 2 := by ring
      have h4 : 1500625 * T ^ 2 ≤ 4 * T ^ 3 := by rw [h3]; nlinarith [pow_pos hT0 2]
      have h5 : 4 * T ^ 3 ≤ 4 * q * T ^ 3 := by
        have hq1'' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
        have := mul_le_mul_of_nonneg_right hq1'' (pow_pos hT0 3).le
        linarith
      nlinarith
    have h2 : Real.log (rexp (1 / 2) * T ^ 3 / U2 T) ≤ 3 * L := by
      have h3 : rexp (1 / 2) * T ^ 3 / U2 T ≤ T ^ 3 := by
        rw [div_le_iff₀ hU0]
        have : rexp (1 / 2) ≤ 2 := by
          have := Real.exp_bound' (x := 1 / 2) (by norm_num) (by norm_num) (n := 3) (by norm_num)
          norm_num [Finset.sum_range_succ, Nat.factorial] at this; linarith
        nlinarith [pow_pos hT0 3]
      have := Real.log_le_log (by positivity) h3
      rw [Real.log_pow] at this; push_cast at this; linarith
    have h20 : 0 ≤ Real.log (rexp (1 / 2) * T ^ 3 / U2 T) := Real.log_nonneg (by
      rw [le_div_iff₀ hU0, one_mul]
      have : 1 ≤ rexp (1 / 2) := Real.one_le_exp (by norm_num)
      have : T ^ 3 = T * T ^ 2 := by ring
      have : 1225 * T ≤ T ^ 3 := by rw [this]; nlinarith [pow_pos hT0 2]
      nlinarith [pow_pos hT0 3])
    have h4 : 1 / rexp 1 ≤ 1 := by rw [div_le_one (Real.exp_pos 1)]; exact Real.one_le_exp (by norm_num)
    have h5 : (U2 T : ℝ) ^ 2 / (4 * q * T ^ 3) * Real.log (rexp (1 / 2) * T ^ 3 / U2 T) + 1 / rexp 1 ≤
        3 * L + 1 := by nlinarith [mul_le_mul h1 h2 h20 (by norm_num)]
    have h6 : 15.761 * (3 * L + 1) ≤ 0.001 * L * T ^ 2 := by
      have hT2 : 3.6e13 ≤ T ^ 2 := by nlinarith
      have hL0 : 0 ≤ L := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hT2 hL0]
    have : 0 ≤ (U2 T : ℝ) ^ 2 / (4 * q * T ^ 3) * Real.log (rexp (1 / 2) * T ^ 3 / U2 T) +
        1 / rexp 1 := by positivity
    nlinarith [mul_le_mul hk h5 this (by norm_num)]
  have tD := b441_second hT hq1 hqQ
  have hL0 : 0 ≤ L := by linarith
  linarith [mul_nonneg (sq_nonneg L) (sq_nonneg T), mul_nonneg hL0 (sq_nonneg T), sq_nonneg T]

set_option maxHeartbeats 4000000 in
/-- (4.50) at the second parameters: `≤ 6.07 L T²`. -/
theorem b450_second {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hc : SecondCase T δ q) :
    bound_4_50 (T ^ 3) δ q (U2 T) (V2 T) ≤ 6.07 * Real.log T * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hq1 := h.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hU := U2_le hT0
  have hU' := U2_ge' hT
  have hU0 := U2_pos hT
  have hV := V2_le hT0
  have hV' := V2_ge' hT
  have hV0 : (0 : ℝ) < V2 T := by linarith
  have hqQ : (q : ℝ) ≤ T ^ 2 / 349 := h.2.2.2.2
  unfold bound_4_50
  simp only []
  -- First term.
  have hl18 : Real.log (T ^ 2 / 18) ≤ 2 * L - 2.89 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
    have := le_log_num (z := 18) 2 0.89 (by norm_num) (by norm_num) (by norm_num [taylor6])
    norm_num at this; push_cast; linarith
  have t1 : T ^ 3 / (2 * q) * minInv c₀ (π * δ) * Real.log (V2 T * q) ≤ 3 * T ^ 2 * (2 * L - 2.89) := by
    rcases hc with hc | hc
    · -- `q > T/6`: monotonicity of `log(Vq)/q`.
      have hmi : minInv c₀ (π * δ) ≤ 1 := by
        unfold minInv; split_ifs
        · exact le_rfl
        · exact min_le_left _ _
      have he : rexp 1 ≤ V2 T * (T / 6) := by
        have := Real.exp_one_lt_d9; nlinarith
      have hmono := log_mul_div_anti hV0 (by positivity : (0 : ℝ) < T / 6) hc.le he
      have hlV0 : 0 ≤ Real.log (V2 T * q) := Real.log_nonneg (by nlinarith)
      have h1 : T ^ 3 / (2 * q) * Real.log (V2 T * q) ≤ 3 * T ^ 2 * Real.log (V2 T * (T / 6)) := by
        have e1 : T ^ 3 / (2 * q) * Real.log (V2 T * q) = T ^ 3 / 2 * (Real.log (V2 T * q) / q) := by
          field_simp
        have e2 : 3 * T ^ 2 * Real.log (V2 T * (T / 6)) = T ^ 3 / 2 * (Real.log (V2 T * (T / 6)) / (T / 6)) := by
          field_simp; ring
        rw [e1, e2]; exact mul_le_mul_of_nonneg_left hmono (by positivity)
      have h2 : Real.log (V2 T * (T / 6)) ≤ 2 * L - 2.89 := by
        have := Real.log_le_log (by positivity) (show V2 T * (T / 6) ≤ T ^ 2 / 18 by nlinarith)
        linarith
      calc T ^ 3 / (2 * q) * minInv c₀ (π * δ) * Real.log (V2 T * q)
          ≤ T ^ 3 / (2 * q) * 1 * Real.log (V2 T * q) := by gcongr
        _ ≤ 3 * T ^ 2 * Real.log (V2 T * (T / 6)) := by rw [mul_one]; exact h1
        _ ≤ _ := by gcongr
    · have hxm : T ^ 3 / (2 * q) * minInv c₀ (π * δ) ≤ 3 * T ^ 2 :=
        (mul_le_mul_of_nonneg_left (minInv_le_delta0 δ) (by positivity)).trans
          (xq_delta0_le hT h (Or.inr hc))
      have hlV0 : 0 ≤ Real.log (V2 T * q) := Real.log_nonneg (by nlinarith)
      have h2 : Real.log (V2 T * q) ≤ 2 * L - 2.89 := by
        have := Real.log_le_log (by positivity) (show V2 T * (q : ℝ) ≤ T ^ 2 / 18 by nlinarith [hc.1])
        linarith
      exact mul_le_mul hxm h2 hlV0 (by positivity)
  -- Second term: negligible.
  have hk : (1 / 4 - 1 / π ^ 2) * c₀ ≤ 4.6876 := by
    have : 0.1013 ≤ 1 / π ^ 2 := by
      have h := Real.pi_lt_d4
      have h2 : π ^ 2 < 3.1416 ^ 2 := pow_lt_pow_left₀ h Real.pi_pos.le (by norm_num)
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have : c₀ = 31.521 := rfl
    nlinarith
  have hk0 : 0 ≤ (1 / 4 - 1 / π ^ 2) * c₀ := by
    have : 1 / π ^ 2 ≤ 1 / 4 := by
      have := Real.pi_gt_d4
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have : (0 : ℝ) < c₀ := by norm_num [c₀]
    nlinarith
  have hD : (U2 T : ℝ) * V2 T ≤ 408.3334 * T ^ 2 := by nlinarith
  have hlV : Real.log (V2 T) ≤ L := Real.log_le_log hV0 (by linarith)
  have hlV0 : 0 ≤ Real.log (V2 T) := Real.log_nonneg (by linarith)
  have hlq : Real.log q ≤ 2 * L := by
    have := Real.log_le_log hq0 (hqQ.trans (show T ^ 2 / 349 ≤ T ^ 2 by
      rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]))
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1'
  have s1 : ((U2 T : ℝ) * V2 T) ^ 2 * Real.log (V2 T) / (2 * q * T ^ 3) ≤ 83368.1 * T * L := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : ((U2 T : ℝ) * V2 T) ^ 2 ≤ (408.3334 * T ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hD 2
    have : ((U2 T : ℝ) * V2 T) ^ 2 * Real.log (V2 T) ≤ (408.3334 * T ^ 2) ^ 2 * L :=
      mul_le_mul h1 hlV hlV0 (by positivity)
    have hL0 : 0 ≤ L := by linarith
    have e : (408.3334 * T ^ 2) ^ 2 * L ≤ 83368.1 * T * L * (2 * q * T ^ 3) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hq1') (pow_pos hT0 4).le) hL0,
        mul_nonneg (pow_pos hT0 4).le hL0]
    linarith
  have s2 : 3 * c₄ / 2 * ((U2 T : ℝ) * V2 T ^ 2 / T ^ 3) ≤ 213 := by
    unfold c₄
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : (V2 T : ℝ) ^ 2 ≤ (T / 3) ^ 2 := pow_le_pow_left₀ hV0.le hV 2
    nlinarith [pow_pos hT0 3, mul_le_mul hU this (by positivity) (by positivity)]
  have s3 : 3 / 2 * (((U2 T : ℝ) + 1) ^ 2 * V2 T / (2 * T ^ 3) * Real.log q) ≤ 750400 * L := by
    have h1 : ((U2 T : ℝ) + 1) ^ 2 * V2 T / (2 * T ^ 3) ≤ 250105 := by
      rw [div_le_iff₀ (by positivity)]
      have : ((U2 T : ℝ) + 1) ^ 2 ≤ (1225.0001 * T) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      nlinarith [pow_pos hT0 3, mul_le_mul this hV (by positivity) (by positivity)]
    nlinarith [mul_le_mul h1 hlq hlq0 (by norm_num)]
  have s0 : 0 ≤ ((U2 T : ℝ) * V2 T) ^ 2 * Real.log (V2 T) / (2 * q * T ^ 3) + 3 * c₄ / 2 *
      ((U2 T : ℝ) * V2 T ^ 2 / T ^ 3) + 3 / 2 * (((U2 T : ℝ) + 1) ^ 2 * V2 T / (2 * T ^ 3) * Real.log q) := by
    unfold c₄; positivity
  have t2 : (1 / 4 - 1 / π ^ 2) * c₀ * (((U2 T : ℝ) * V2 T) ^ 2 * Real.log (V2 T) / (2 * q * T ^ 3) +
      3 * c₄ / 2 * ((U2 T : ℝ) * V2 T ^ 2 / T ^ 3) +
      3 / 2 * (((U2 T : ℝ) + 1) ^ 2 * V2 T / (2 * T ^ 3) * Real.log q)) ≤ 8.67 * T ^ 2 + 0.07 * L * T ^ 2 := by
    have h1 : 83368.1 * T * L + 213 + 750400 * L ≤ 0.0149 * L * T ^ 2 + 1.84 * T ^ 2 := by
      have : 83368.1 * T ≤ 0.0139 * T ^ 2 := by nlinarith
      have : 750400 ≤ 0.001 * T ^ 2 := by nlinarith
      have : 213 ≤ 1.84 * T ^ 2 := by nlinarith
      have hL0 : 0 ≤ L := by linarith
      nlinarith
    have h2 := mul_le_mul hk (show _ ≤ 0.0149 * L * T ^ 2 + 1.84 * T ^ 2 by linarith) s0 (by norm_num)
    have hL0 : 0 ≤ L := by linarith
    nlinarith [mul_nonneg hL0 (sq_nonneg T), sq_nonneg T]
  have hL0 : 0 ≤ L := by linarith
  nlinarith [mul_nonneg hL0 (sq_nonneg T), sq_nonneg T]

end TernaryGoldbach.MinorArcs
