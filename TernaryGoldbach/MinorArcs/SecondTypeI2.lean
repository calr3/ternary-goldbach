import TernaryGoldbach.MinorArcs.SecondTypeI1

/-!
# Type I at the second parameters: (4.51), (4.52) and the totals

With `D = UV ≤ 408.3334 T²`, `L = log T`:
* `b451_second` (case (a), `|δ| ≤ 1/2c₂`): `(4.51) ≤ (0.031 L² + 3003.1 L + 8298) T²`;
* `b452_second` (`ε = 0.01`, `|δ| ≥ 1/2c₂`): `(4.52) ≤ (3155.7 L + 8391.5) T²`;
* **`typeI_second`**: `|S_{I,1}| + |S_{I,2}| ≤ (0.0716 L² + 3175.9 L + 8399.2) T²`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

theorem D2_facts {T : ℝ} (hT : 6e6 ≤ T) :
    408.32 * T ^ 2 ≤ (U2 T : ℝ) * V2 T ∧ (U2 T : ℝ) * V2 T ≤ 408.3334 * T ^ 2 ∧
      Real.log ((U2 T : ℝ) * V2 T) ≤ 2 * Real.log T + 6.0122 := by
  have hT0 : 0 < T := by linarith
  have hU := U2_le hT0
  have hU' := U2_ge' hT
  have hV := V2_le hT0
  have hV' := V2_ge' hT
  have hV0 : (0 : ℝ) < V2 T := by linarith
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have h1 : (U2 T : ℝ) * V2 T ≤ 408.3334 * T ^ 2 := by nlinarith
  have := Real.log_le_log (by nlinarith) h1
  rw [Real.log_mul (show (408.3334 : ℝ) ≠ 0 by norm_num) (show T ^ 2 ≠ 0 by positivity),
    Real.log_pow] at this
  have h2 := log_le_num (z := 408.3334) 6 0.0122 (by norm_num) (by norm_num) (by norm_num [taylor6])
  norm_num at h2; push_cast at this; linarith

theorem c1_second {T : ℝ} (hT : 6e6 ≤ T) :
    2 * √(c₀ * (1 + eta2'L1 / (T ^ 3 / ((U2 T : ℝ) * V2 T)))) / π ≤ 3.575 := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hD1, hD2, -⟩ := D2_facts hT
  have hη := eta2'L1_le
  have hη0 := eta2'L1_pos
  have hD0 : (0 : ℝ) < (U2 T : ℝ) * V2 T := by nlinarith
  have hc : eta2'L1 / (T ^ 3 / ((U2 T : ℝ) * V2 T)) ≤ 0.000378 := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : eta2'L1 * ((U2 T : ℝ) * V2 T) ≤ 5.5452 * (408.3334 * T ^ 2) :=
      mul_le_mul hη hD2 hD0.le (by norm_num)
    have : T ^ 3 = T * T ^ 2 := by ring
    nlinarith [pow_pos hT0 2]
  have hc0 : 0 ≤ eta2'L1 / (T ^ 3 / ((U2 T : ℝ) * V2 T)) := by positivity
  refine (two_sqrt_c0_mul_le (by linarith)).trans ?_
  have : √(1 + eta2'L1 / (T ^ 3 / ((U2 T : ℝ) * V2 T))) ≤ 1.000189 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  nlinarith

theorem c1_second' {T : ℝ} (hT : 6e6 ≤ T) :
    1 + eta2'L1 / (T ^ 3 / ((U2 T : ℝ) * V2 T)) ≤ 1.000378 := by
  have hT0 : 0 < T := by linarith
  obtain ⟨hD1, hD2, -⟩ := D2_facts hT
  have hη := eta2'L1_le
  have hη0 := eta2'L1_pos
  have hD0 : (0 : ℝ) < (U2 T : ℝ) * V2 T := by nlinarith
  have hc : eta2'L1 / (T ^ 3 / ((U2 T : ℝ) * V2 T)) ≤ 0.000378 := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : eta2'L1 * ((U2 T : ℝ) * V2 T) ≤ 5.5452 * (408.3334 * T ^ 2) :=
      mul_le_mul hη hD2 hD0.le (by norm_num)
    have : T ^ 3 = T * T ^ 2 := by ring
    nlinarith [pow_pos hT0 2]
  linarith

/-- `y log(C/y) ≤ Y log(C/Y)` for `0 < y ≤ Y ≤ C/e`. -/
theorem mul_log_div_mono {y Y C : ℝ} (hy : 0 < y) (hyY : y ≤ Y) (hYC : Y * rexp 1 ≤ C) :
    y * Real.log (C / y) ≤ Y * Real.log (C / Y) := by
  have hY : 0 < Y := by linarith
  have hC : 0 < C := lt_of_lt_of_le (by positivity) hYC
  have h1 : 1 ≤ Real.log (C / Y) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hY]; linarith
  have h2 : Real.log (Y / y) ≤ Y / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have e : Real.log (C / y) = Real.log (C / Y) + Real.log (Y / y) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  rw [e]
  have h3 : y * Real.log (Y / y) ≤ Y - y := by
    have := mul_le_mul_of_nonneg_left h2 hy.le
    rw [mul_sub, mul_div_cancel₀ _ hy.ne', mul_one] at this; exact this
  nlinarith

set_option maxHeartbeats 8000000 in
/-- (4.51) at the second parameters in case (a). -/
theorem b451_second {T : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : T / 6 < q) (hqQ : (q : ℝ) ≤ T ^ 2 / 349) :
    bound_4_51 (T ^ 3) q (U2 T) (V2 T) ≤
      (0.031 * Real.log T ^ 2 + 3003.1 * Real.log T + 8298) * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hL0 : 0 ≤ L := by linarith
  have hsT := sqrt_ge_2449 hT
  have hss : √T * √T = T := Real.mul_self_sqrt hT0.le
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨hD1, hD2, hlD⟩ := D2_facts hT
  have hA := c1_second hT
  have hc1 := c1_second' hT
  obtain ⟨hc2a, hc2b⟩ := c₂_bounds
  obtain ⟨hc0a, hc0b⟩ := sqrt_c₀_bounds
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  have hη := eta2'L1_le
  have hη0 := eta2'L1_pos
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hq349 : (q : ℝ) * 349 ≤ T ^ 2 := by rwa [le_div_iff₀ (by norm_num)] at hqQ
  unfold bound_4_51
  simp only []
  set D := (U2 T : ℝ) * V2 T with hDdef
  have hD0 : 0 < D := by nlinarith
  set c₁ := 1 + eta2'L1 / (T ^ 3 / D)
  have hc10 : 1 ≤ c₁ := by
    have : 0 ≤ eta2'L1 / (T ^ 3 / D) := by positivity
    show 1 ≤ 1 + eta2'L1 / (T ^ 3 / D); linarith
  have hA0 : 0 ≤ 2 * √(c₀ * c₁) / π := by positivity
  have hlD0 : 0 ≤ Real.log D := Real.log_nonneg (by nlinarith)
  -- Main term `D log(D/√e)`.
  have t1 : D * Real.log (D / √(rexp 1)) ≤ 408.3334 * T ^ 2 * (2 * L + 5.5122) := by
    have h1 : Real.log (D / √(rexp 1)) = Real.log D - 1 / 2 := by
      rw [Real.log_div hD0.ne' (Real.sqrt_pos.2 (Real.exp_pos 1)).ne', Real.log_sqrt
        (Real.exp_pos 1).le, Real.log_exp]
    have h2 : 0 ≤ Real.log D - 1 / 2 := by
      have : 1 ≤ Real.log D := by
        rw [Real.le_log_iff_exp_le hD0]; nlinarith
      linarith
    rw [h1]; exact mul_le_mul hD2 (by linarith) h2 (by positivity)
  -- `q(√3 log 3D + (2 + log D/2) log⁺(2D/q))`.
  have t2 : (q : ℝ) * (√3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2))) ≤
      (0.0028654 * L ^ 2 + 0.048617 * L + 0.15718) * T ^ 2 := by
    have hs3 : √3 ≤ 1.7321 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hl3 : Real.log (3 * D) ≤ 2 * L + 7.111 := by
      rw [Real.log_mul (by norm_num) hD0.ne']
      have := log_le_num (z := 3) 1 0.0987 (by norm_num) (by norm_num) (by norm_num [taylor6])
      norm_num at this; linarith
    have hl30 : 0 ≤ Real.log (3 * D) := Real.log_nonneg (by nlinarith)
    have hlp : logPlus (D / (q / 2)) ≤ L + 8.497 := by
      unfold logPlus
      refine max_le ?_ (by linarith)
      have h1 : D / (q / 2) ≤ 4900.0008 * T := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have h2 : Real.log (4900.0008 * T) ≤ L + 8.497 := by
        rw [Real.log_mul (by norm_num) hT0.ne']
        have := log_le_num (z := 4900.0008) 8 0.497 (by norm_num) (by norm_num) (by norm_num [taylor6])
        norm_num at this ⊢; linarith
      exact (Real.log_le_log (by positivity) h1).trans h2
    have hlp0 : 0 ≤ logPlus (D / (q / 2)) := logPlus_nonneg _
    have hin : √3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2)) ≤
        1.7321 * (2 * L + 7.111) + (L + 5.0061) * (L + 8.497) := by
      have h1 : √3 * Real.log (3 * D) ≤ 1.7321 * (2 * L + 7.111) :=
        mul_le_mul hs3 hl3 hl30 (by norm_num)
      have h2 : (2 + Real.log D / 2) * logPlus (D / (q / 2)) ≤ (L + 5.0061) * (L + 8.497) :=
        mul_le_mul (by linarith) hlp hlp0 (by linarith)
      linarith
    have hin0 : 0 ≤ √3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2)) := by
      positivity
    calc (q : ℝ) * (√3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2)))
        ≤ (T ^ 2 / 349) * (1.7321 * (2 * L + 7.111) + (L + 5.0061) * (L + 8.497)) :=
          mul_le_mul hqQ hin hin0 (by positivity)
      _ ≤ _ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
          have h1 := mul_nonneg (sq_nonneg L) (sq_nonneg T)
          nlinarith [sq_nonneg T, mul_nonneg hL0 (sq_nonneg T)]
  have tA : 2 * √(c₀ * c₁) / π * (D * Real.log (D / √(rexp 1)) +
      (q : ℝ) * (√3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2)))) ≤
      3.575 * (408.3334 * T ^ 2 * (2 * L + 5.5122) +
        (0.0028654 * L ^ 2 + 0.048617 * L + 0.15718) * T ^ 2) := by
    have h0 : 0 ≤ D * Real.log (D / √(rexp 1)) +
        (q : ℝ) * (√3 * Real.log (3 * D) + (2 + Real.log D / 2) * logPlus (D / (q / 2))) := by
      have : 0 ≤ Real.log (D / √(rexp 1)) := Real.log_nonneg (by
        rw [le_div_iff₀ (Real.sqrt_pos.2 (Real.exp_pos 1)), one_mul]
        have : √(rexp 1) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; linarith
        nlinarith)
      have : 0 ≤ logPlus (D / (q / 2)) := logPlus_nonneg _
      have : 0 ≤ Real.log (3 * D) := Real.log_nonneg (by nlinarith)
      positivity
    exact mul_le_mul hA (by linarith) h0 (by norm_num)
  -- `(3c₁/2)(x/q) log D log⁺(qD/c₂x)`.
  have tB : 3 * c₁ / 2 * (T ^ 3 / q) * Real.log D * logPlus (D / (c₂ * T ^ 3 / q)) ≤
      (83.22 * L + 250.14) * T ^ 2 := by
    set w := D / (c₂ * T ^ 3 / q) with hwdef
    set w₀ := D / (c₂ * T ^ 3 / (T / 6)) with hw₀def
    have e6 : c₂ * T ^ 3 / (T / 6) = 6 * c₂ * T ^ 2 := by field_simp
    have hw₀e : rexp 1 ≤ w₀ := by
      rw [hw₀def, le_div_iff₀ (by positivity), e6]
      have : rexp 1 * (6 * c₂ * T ^ 2) ≤ 2.72 * (6 * 0.672 * T ^ 2) := by
        have : 6 * c₂ * T ^ 2 ≤ 6 * 0.672 * T ^ 2 := by nlinarith [sq_nonneg T]
        exact mul_le_mul (by linarith) this (by positivity) (by norm_num)
      nlinarith [sq_nonneg T]
    have hww₀ : w₀ ≤ w := by
      rw [hwdef, hw₀def]
      apply div_le_div_of_nonneg_left hD0.le (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hq.le
    have hw1 : 1 ≤ w := le_trans (by linarith) (hw₀e.trans hww₀)
    have hlog : logPlus w = Real.log w := logPlus_le_log hw1
    have hmono := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hw₀e) (Set.mem_Ici.2 (hw₀e.trans hww₀))
      hww₀
    simp only at hmono
    have hw₀u : Real.log w₀ ≤ 4.6209 := by
      have h1 : w₀ ≤ 101.576 := by
        rw [hw₀def, div_le_iff₀ (by positivity), e6]
        have : 101.576 * (6 * 0.67 * T ^ 2) ≤ 101.576 * (6 * c₂ * T ^ 2) := by
          have : 6 * 0.67 * T ^ 2 ≤ 6 * c₂ * T ^ 2 := by nlinarith [sq_nonneg T]
          linarith
        nlinarith [sq_nonneg T]
      have h2 : Real.log 101.576 ≤ 4.6209 := by
        have := log_le_num (z := 101.576) 4 0.6209 (by norm_num) (by norm_num) (by norm_num [taylor6])
        norm_num at this ⊢; linarith
      exact (Real.log_le_log (by linarith [Real.exp_pos 1]) h1).trans h2
    have hw0 : 0 < w := by linarith
    have hw₀0 : 0 < w₀ := by linarith
    have e1 : T ^ 3 / q * Real.log w = D / c₂ * (Real.log w / w) := by
      rw [hwdef]; field_simp
    have e2 : D / c₂ * (Real.log w₀ / w₀) = 6 * T ^ 2 * Real.log w₀ := by
      rw [hw₀def]; field_simp
    have key : T ^ 3 / q * logPlus w ≤ 6 * T ^ 2 * 4.6209 := by
      rw [hlog, e1]
      calc D / c₂ * (Real.log w / w) ≤ D / c₂ * (Real.log w₀ / w₀) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = 6 * T ^ 2 * Real.log w₀ := e2
        _ ≤ _ := by gcongr
    have key0 : 0 ≤ T ^ 3 / q * logPlus w := mul_nonneg (by positivity) (logPlus_nonneg _)
    calc 3 * c₁ / 2 * (T ^ 3 / q) * Real.log D * logPlus w
        = 3 * c₁ / 2 * Real.log D * (T ^ 3 / q * logPlus w) := by ring
      _ ≤ 3 * 1.000378 / 2 * (2 * L + 6.0122) * (6 * T ^ 2 * 4.6209) := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg T, mul_nonneg hL0 (sq_nonneg T)]
  -- `(2|η'|/π) q max(1, log(…)) log⁺(q/2)`.
  have tC : 2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3))) *
      logPlus (q / 2) ≤ 0.020232 * L ^ 2 * T ^ 2 := by
    have hmax : max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3))) ≤ L := by
      refine max_le (by linarith) ?_
      have he3 : rexp 3 ≤ 20.1 := by
        calc rexp 3 = rexp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
          _ ≤ 20.1 := by norm_num
      have harg : c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3) ≤ T := by
        rw [div_le_iff₀ (by positivity)]
        have hq2 : (q : ℝ) ^ 2 ≤ T ^ 4 / 121801 := by
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
    have hm0 : 0 ≤ max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3))) :=
      le_trans zero_le_one (le_max_left _ _)
    have hlp : logPlus (q / 2) ≤ 2 * L := by
      unfold logPlus
      refine max_le ?_ (by linarith)
      have h1 : (q : ℝ) / 2 ≤ T ^ 2 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith [sq_nonneg T]
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hη' : 2 * eta2'L1 / π ≤ 3.5304 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    calc 2 * eta2'L1 / π * q * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * T ^ 3))) *
          logPlus (q / 2)
        ≤ 3.5304 * (T ^ 2 / 349) * L * (2 * L) := by
          have : 0 ≤ logPlus (q / 2) := logPlus_nonneg _
          gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg T)]
  -- the `√x` terms.
  have hsx : √(2 * T ^ 3 / c₂) ≤ 1.7278 * (T * √T) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, sq (√T), hss, div_le_iff₀ (by linarith)]
    nlinarith [pow_pos hT0 3]
  have tD : 3 * c₁ / 2 * √(2 * T ^ 3 / c₂) * (Real.log (3 * √(c₂ * T ^ 3 / 2)) + 1) ≤
      (0.00159 * L + 0.00165) * T ^ 2 := by
    have hl : Real.log (3 * √(c₂ * T ^ 3 / 2)) ≤ 1.5 * L + 0.554 := by
      have h1 : 3 * √(c₂ * T ^ 3 / 2) ≤ 1.739 * (T * √T) := by
        have : √(c₂ * T ^ 3 / 2) ≤ 0.57966 * (T * √T) := by
          rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, sq (√T), hss]
          nlinarith [pow_pos hT0 3]
        have : 0 ≤ T * √T := by positivity
        linarith
      have h2 : Real.log (1.739 * (T * √T)) = Real.log 1.739 + 1.5 * L := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul hT0.ne' (by positivity),
          Real.log_sqrt hT0.le]; ring
      have h3 : Real.log 1.739 ≤ 0.554 := by
        have := log_le_num (z := 1.739) 0 0.554 (by norm_num) (by norm_num) (by norm_num [taylor6])
        norm_num at this ⊢; linarith
      have := Real.log_le_log (by positivity) h1
      linarith
    have hl0 : 0 ≤ Real.log (3 * √(c₂ * T ^ 3 / 2)) + 1 := by
      have : 0 ≤ Real.log (3 * √(c₂ * T ^ 3 / 2)) := Real.log_nonneg (by
        have : 1 ≤ √(c₂ * T ^ 3 / 2) := by
          rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [pow_pos hT0 3]
        linarith)
      linarith
    calc 3 * c₁ / 2 * √(2 * T ^ 3 / c₂) * (Real.log (3 * √(c₂ * T ^ 3 / 2)) + 1)
        ≤ 3 * 1.000378 / 2 * (1.7278 * (T * √T)) * (1.5 * L + 0.554 + 1) := by gcongr
      _ ≤ _ := by
          have : T * √T * 2449 ≤ T ^ 2 := by nlinarith
          nlinarith
  have tE : 2 * √c₀ / π * √(2 * c₂ * T ^ 3) * (2 + 12 * Real.log (5 * D)) + 5 * c₀ / (6 * π ^ 2) ≤
      (0.04061 * L + 0.1583) * T ^ 2 := by
    have hk : 2 * √c₀ / π ≤ 3.5744 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hsx2 : √(2 * c₂ * T ^ 3) ≤ 1.15932 * (T * √T) := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, sq (√T), hss]
      nlinarith [pow_pos hT0 3]
    have hl5 : Real.log (5 * D) ≤ 2 * L + 7.6217 := by
      rw [Real.log_mul (by norm_num) hD0.ne']
      have := log_le_num (z := 5) 1 0.6095 (by norm_num) (by norm_num) (by norm_num [taylor6])
      norm_num at this; linarith
    have hl50 : 0 ≤ Real.log (5 * D) := Real.log_nonneg (by nlinarith)
    have h5c : 5 * c₀ / (6 * π ^ 2) ≤ 2.7 := by
      have : c₀ = 31.521 := rfl
      rw [this, div_le_iff₀ (by positivity)]; nlinarith
    calc 2 * √c₀ / π * √(2 * c₂ * T ^ 3) * (2 + 12 * Real.log (5 * D)) + 5 * c₀ / (6 * π ^ 2)
        ≤ 3.5744 * (1.15932 * (T * √T)) * (2 + 12 * (2 * L + 7.6217)) + 2.7 := by gcongr
      _ ≤ _ := by
          have : T * √T * 2449 ≤ T ^ 2 := by nlinarith
          have : 2.7 ≤ 0.0001 * T ^ 2 := by nlinarith
          nlinarith
  linarith [mul_nonneg (sq_nonneg L) (sq_nonneg T), mul_nonneg hL0 (sq_nonneg T), sq_nonneg T]

end TernaryGoldbach.MinorArcs
