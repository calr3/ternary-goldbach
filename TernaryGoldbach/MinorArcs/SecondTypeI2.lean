import TernaryGoldbach.MinorArcs.SecondTypeI1
import TernaryGoldbach.MinorArcs.TypeI2Rest

variable [Fact TernaryGoldbach.RHUpTo]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# Type I at the second parameters: (4.51), (4.52) and the totals

With `D = UV ≤ 408.3334 T²`, `L = log T`:
* `b451_second` (case (a), `|δ| ≤ 1/2c₂`): `(4.51) ≤ (0.031 L² + 3025.5 L + 8360) T²`;
* `b452_second` (`ε = 0.01`, `|δ| ≥ 1/2c₂`): `(4.52) ≤ (3179.7 L + 8455.3) T²`;
* **`typeI_second`**: `|S_{I,1}| + |S_{I,2}| ≤ (0.0717 L² + 3199.9 L + 8471.0) T²`.
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
    2 * √(c₀ * (1 + eta2'L1 / (T ^ 3 / ((U2 T : ℝ) * V2 T)))) / π ≤ 3.6021 := by
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
      (0.031 * Real.log T ^ 2 + 3025.5 * Real.log T + 8360) * T ^ 2 := by
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
      3.6021 * (408.3334 * T ^ 2 * (2 * L + 5.5122) +
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
      (83.31 * L + 250.44) * T ^ 2 := by
    set w := D / (c₂ * T ^ 3 / q) with hwdef
    set w₀ := D / (c₂ * T ^ 3 / (T / 6)) with hw₀def
    have e6 : c₂ * T ^ 3 / (T / 6) = 6 * c₂ * T ^ 2 := by field_simp
    have hw₀e : rexp 1 ≤ w₀ := by
      rw [hw₀def, le_div_iff₀ (by positivity), e6]
      have : rexp 1 * (6 * c₂ * T ^ 2) ≤ 2.72 * (6 * 0.6665 * T ^ 2) := by
        have : 6 * c₂ * T ^ 2 ≤ 6 * 0.6665 * T ^ 2 := by nlinarith [sq_nonneg T]
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
    have hw₀u : Real.log w₀ ≤ 4.6264 := by
      have h1 : w₀ ≤ 102.13 := by
        rw [hw₀def, div_le_iff₀ (by positivity), e6]
        have : 102.13 * (6 * 0.6664 * T ^ 2) ≤ 102.13 * (6 * c₂ * T ^ 2) := by
          have : 6 * 0.6664 * T ^ 2 ≤ 6 * c₂ * T ^ 2 := by nlinarith [sq_nonneg T]
          linarith
        nlinarith [sq_nonneg T]
      have h2 : Real.log 102.13 ≤ 4.6264 := by
        have := log_le_num (z := 102.13) 4 0.6264 (by norm_num) (by norm_num) (by norm_num [taylor6])
        norm_num at this ⊢; linarith
      exact (Real.log_le_log (by linarith [Real.exp_pos 1]) h1).trans h2
    have hw0 : 0 < w := by linarith
    have hw₀0 : 0 < w₀ := by linarith
    have e1 : T ^ 3 / q * Real.log w = D / c₂ * (Real.log w / w) := by
      rw [hwdef]; field_simp
    have e2 : D / c₂ * (Real.log w₀ / w₀) = 6 * T ^ 2 * Real.log w₀ := by
      rw [hw₀def]; field_simp
    have key : T ^ 3 / q * logPlus w ≤ 6 * T ^ 2 * 4.6264 := by
      rw [hlog, e1]
      calc D / c₂ * (Real.log w / w) ≤ D / c₂ * (Real.log w₀ / w₀) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ = 6 * T ^ 2 * Real.log w₀ := e2
        _ ≤ _ := by gcongr
    have key0 : 0 ≤ T ^ 3 / q * logPlus w := mul_nonneg (by positivity) (logPlus_nonneg _)
    calc 3 * c₁ / 2 * (T ^ 3 / q) * Real.log D * logPlus w
        = 3 * c₁ / 2 * Real.log D * (T ^ 3 / q * logPlus w) := by ring
      _ ≤ 3 * 1.000378 / 2 * (2 * L + 6.0122) * (6 * T ^ 2 * 4.6264) := by gcongr
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
        have : c₀ * rexp 3 * q ^ 2 ≤ 32 * 20.1 * (T ^ 4 / 121801) := by
          have : c₀ = 32 := rfl
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
  have hsx : √(2 * T ^ 3 / c₂) ≤ 1.7325 * (T * √T) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, sq (√T), hss, div_le_iff₀ (by linarith)]
    nlinarith [pow_pos hT0 3]
  have tD : 3 * c₁ / 2 * √(2 * T ^ 3 / c₂) * (Real.log (3 * √(c₂ * T ^ 3 / 2)) + 1) ≤
      (0.0016 * L + 0.00165) * T ^ 2 := by
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
        ≤ 3 * 1.000378 / 2 * (1.7325 * (T * √T)) * (1.5 * L + 0.554 + 1) := by gcongr
      _ ≤ _ := by
          have : T * √T * 2449 ≤ T ^ 2 := by nlinarith
          nlinarith
  have tE : 2 * √c₀ / π * √(2 * c₂ * T ^ 3) * (2 + 12 * Real.log (5 * D)) + 5 * c₀ / (6 * π ^ 2) ≤
      (0.04092 * L + 0.1595) * T ^ 2 := by
    have hk : 2 * √c₀ / π ≤ 3.6015 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hsx2 : √(2 * c₂ * T ^ 3) ≤ 1.15932 * (T * √T) := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, mul_pow, sq (√T), hss]
      nlinarith [pow_pos hT0 3]
    have hl5 : Real.log (5 * D) ≤ 2 * L + 7.6217 := by
      rw [Real.log_mul (by norm_num) hD0.ne']
      have := log_le_num (z := 5) 1 0.6095 (by norm_num) (by norm_num) (by norm_num [taylor6])
      norm_num at this; linarith
    have hl50 : 0 ≤ Real.log (5 * D) := Real.log_nonneg (by nlinarith)
    have h5c : 5 * c₀ / (6 * π ^ 2) ≤ 2.71 := by
      have : c₀ = 32 := rfl
      rw [this, div_le_iff₀ (by positivity)]; nlinarith
    calc 2 * √c₀ / π * √(2 * c₂ * T ^ 3) * (2 + 12 * Real.log (5 * D)) + 5 * c₀ / (6 * π ^ 2)
        ≤ 3.6015 * (1.15932 * (T * √T)) * (2 + 12 * (2 * L + 7.6217)) + 2.71 := by gcongr
      _ ≤ _ := by
          have : T * √T * 2449 ≤ T ^ 2 := by nlinarith
          have : 2.71 ≤ 0.0001 * T ^ 2 := by nlinarith
          nlinarith
  linarith [mul_nonneg (sq_nonneg L) (sq_nonneg T), mul_nonneg hL0 (sq_nonneg T), sq_nonneg T]

set_option maxHeartbeats 8000000 in
/-- (4.52) at the second parameters (`ε = 0.01`, `|δ| ≥ 1/2c₂`). -/
theorem b452_second {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hc : SecondCase T δ q) (hδ : 1 / (2 * c₂) ≤ |δ|) :
    bound_4_52 (T ^ 3) δ q (U2 T) (V2 T) (Q2 T) 0.01 ≤
      (3179.7 * Real.log T + 8455.3) * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL := fifteen_six_le_log hT
  have hL0 : 0 ≤ L := by linarith
  have hsT := sqrt_ge_2449 hT
  have hq1 := h.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqQ : (q : ℝ) ≤ T ^ 2 / 349 := h.2.2.2.2
  have hq349 : (q : ℝ) * 349 ≤ T ^ 2 := by rwa [le_div_iff₀ (by norm_num)] at hqQ
  obtain ⟨hD1, hD2, hlD⟩ := D2_facts hT
  have hA := c1_second hT
  have hc1 := c1_second' hT
  obtain ⟨hc2a, hc2b⟩ := c₂_bounds
  have hpi := Real.pi_gt_d4
  have he := Real.exp_one_lt_d9
  have hδ0 : 0 < |δ| := lt_of_lt_of_le (by positivity) hδ
  -- `y = x/|δ|q ∈ [T²/349, 8.064 T²]`.
  have hy_lo : T ^ 2 / 349 ≤ T ^ 3 / (|δ| * q) := by
    have hδQ := h.2.2.2.1
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < T ^ 3), div_le_div_iff₀ (by positivity)
      (by unfold Q2; positivity), one_mul] at hδQ
    unfold Q2 at hδQ
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [pow_pos hT0 2]
  have hy_up : T ^ 3 / (|δ| * q) ≤ 8.064 * T ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    rcases hc with hc | ⟨-, -, hδq⟩
    · have h1 : 1 / (2 * c₂) * (T / 6) ≤ |δ| * q := mul_le_mul hδ hc.le (by positivity) hδ0.le
      have h2 : 1 / (2 * 0.6665) * (T / 6) ≤ 1 / (2 * c₂) * (T / 6) := by
        gcongr
      have : T ^ 3 ≤ 8.064 * T ^ 2 * (1 / (2 * 0.6665) * (T / 6)) := by
        have : T ^ 3 = T * T ^ 2 := by ring
        rw [this]; nlinarith [pow_pos hT0 2]
      nlinarith [pow_pos hT0 2]
    · have : T ^ 3 = T * T ^ 2 := by ring
      rw [this]; nlinarith [pow_pos hT0 2]
  unfold bound_4_52
  simp only []
  set D := (U2 T : ℝ) * V2 T with hDdef
  have hD0 : 0 < D := by nlinarith
  set c₁ := 1 + eta2'L1 / (T ^ 3 / D)
  have hc10 : 1 ≤ c₁ := by
    have : 0 ≤ eta2'L1 / (T ^ 3 / D) := div_nonneg eta2'L1_pos.le (div_nonneg (by positivity) hD0.le)
    show 1 ≤ 1 + eta2'L1 / (T ^ 3 / D); linarith
  set y := T ^ 3 / (|δ| * q) with hydef
  have hy0 : 0 < y := by positivity
  have hlD0 : 0 ≤ Real.log D := Real.log_nonneg (by nlinarith)
  -- `log⁺(2D/y)`.
  have h2Dy1 : 1 ≤ 2 * D / y := by rw [le_div_iff₀ hy0]; nlinarith
  have hlp : logPlus (2 * D / y) = Real.log (2 * D / y) := logPlus_le_log h2Dy1
  have hlp0 : 0 ≤ Real.log (2 * D / y) := Real.log_nonneg h2Dy1
  have hlp1 : Real.log (2 * D / y) ≤ 12.5604 := by
    have h1 : 2 * D / y ≤ 285016.8 := by
      rw [div_le_iff₀ hy0]; nlinarith [sq_nonneg T]
    have h2 : Real.log 285016.8 ≤ 12.5604 := by
      have := log_le_num (z := 285016.8) 12 0.5604 (by norm_num) (by norm_num) (by norm_num [taylor6])
      norm_num at this ⊢; linarith
    exact (Real.log_le_log (by positivity) h1).trans h2
  have hylog : y * Real.log (2 * D / y) ≤ 37.239 * T ^ 2 := by
    have h1 := mul_log_div_mono hy0 hy_up (show 8.064 * T ^ 2 * rexp 1 ≤ 2 * D by nlinarith)
    have h2 : Real.log (2 * D / (8.064 * T ^ 2)) ≤ 4.6179 := by
      have h3 : 2 * D / (8.064 * T ^ 2) ≤ 101.2732 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg T]
      have h4 : Real.log 101.2732 ≤ 4.6179 := by
        have := log_le_num (z := 101.2732) 4 0.6179 (by norm_num) (by norm_num) (by norm_num [taylor6])
        norm_num at this ⊢; linarith
      exact (Real.log_le_log (by positivity) h3).trans h4
    calc y * Real.log (2 * D / y) ≤ 8.064 * T ^ 2 * Real.log (2 * D / (8.064 * T ^ 2)) := h1
      _ ≤ 8.064 * T ^ 2 * 4.6179 := by gcongr
      _ ≤ _ := by nlinarith [sq_nonneg T]
  -- `Y ≤ y + 1`.
  set Y := min ((⌊y⌋₊ : ℝ) + 1) (2 * D)
  have hY : Y ≤ y + 1 := (min_le_left _ _).trans (by linarith [Nat.floor_le hy0.le])
  have hY0 : 0 ≤ Y := le_min (by positivity) (by positivity)
  -- the bracket.
  have hl5 : Real.log (5 * D) ≤ 2 * L + 7.6217 := by
    rw [Real.log_mul (by norm_num) hD0.ne']
    have := log_le_num (z := 5) 1 0.6095 (by norm_num) (by norm_num) (by norm_num [taylor6])
    norm_num at this; linarith
  have hl50 : 0 ≤ Real.log (5 * D) := Real.log_nonneg (by nlinarith)
  have hs302 : √(3 + 2 * 0.01) ≤ 1.73782 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hbrA : √(3 + 2 * 0.01) * Real.log (5 * D) + 1 / 2 ≤ 3.47564 * L + 13.74549 := by
    have := mul_le_mul hs302 hl5 hl50 (by norm_num); nlinarith
  have hbrA0 : 0 ≤ √(3 + 2 * 0.01) * Real.log (5 * D) + 1 / 2 := by positivity
  have hYbr : Y * (√(3 + 2 * 0.01) * Real.log (5 * D) + 1 / 2 + (2 + Real.log D / 2) *
      logPlus (2 * D / y)) ≤ (65.2667 * L + 297.266) * T ^ 2 + (16.037 * L + 76.63) := by
    rw [hlp]
    have hB : 2 + Real.log D / 2 ≤ L + 5.0061 := by linarith
    have hB0 : 0 ≤ 2 + Real.log D / 2 := by linarith
    have h1 : Y * (√(3 + 2 * 0.01) * Real.log (5 * D) + 1 / 2) ≤
        (8.064 * T ^ 2 + 1) * (3.47564 * L + 13.74549) :=
      mul_le_mul (by linarith) hbrA hbrA0 (by positivity)
    have h2 : Y * Real.log (2 * D / y) ≤ 37.239 * T ^ 2 + 12.5604 := by
      have := mul_le_mul_of_nonneg_right hY hlp0
      nlinarith
    have h3 : Y * ((2 + Real.log D / 2) * Real.log (2 * D / y)) ≤
        (L + 5.0061) * (37.239 * T ^ 2 + 12.5604) := by
      rw [show Y * ((2 + Real.log D / 2) * Real.log (2 * D / y)) =
        (2 + Real.log D / 2) * (Y * Real.log (2 * D / y)) by ring]
      exact mul_le_mul hB h2 (mul_nonneg hY0 hlp0) (by linarith)
    nlinarith [sq_nonneg T, mul_nonneg hL0 (sq_nonneg T)]
  have hYbr0 : 0 ≤ Y * (√(3 + 2 * 0.01) * Real.log (5 * D) + 1 / 2 + (2 + Real.log D / 2) *
      logPlus (2 * D / y)) := by
    have : 0 ≤ logPlus (2 * D / y) := logPlus_nonneg _
    have : 0 ≤ 2 + Real.log D / 2 := by linarith
    positivity
  have hDl : D * Real.log (D / rexp 1) ≤ 408.3334 * T ^ 2 * (2 * L + 5.0122) := by
    have h1 : Real.log (D / rexp 1) = Real.log D - 1 := by
      rw [Real.log_div hD0.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have h2 : 0 ≤ Real.log D - 1 := by
      have : 1 ≤ Real.log D := by rw [Real.le_log_iff_exp_le hD0]; nlinarith
      linarith
    rw [h1]; exact mul_le_mul hD2 (by linarith) h2 (by positivity)
  have hDl0 : 0 ≤ D * Real.log (D / rexp 1) := by
    have : 0 ≤ Real.log (D / rexp 1) := Real.log_nonneg (by rw [le_div_iff₀ (Real.exp_pos 1)]; nlinarith)
    positivity
  have tA : 2 * √(c₀ * c₁) / π * (D * Real.log (D / rexp 1) + (1 + 0.01) * Y *
      (√(3 + 2 * 0.01) * Real.log (5 * D) + 1 / 2 + (2 + Real.log D / 2) * logPlus (2 * D / y))) ≤
      (3179.2 * L + 8454.0) * T ^ 2 := by
    have h1 : D * Real.log (D / rexp 1) + (1 + 0.01) * Y *
        (√(3 + 2 * 0.01) * Real.log (5 * D) + 1 / 2 + (2 + Real.log D / 2) * logPlus (2 * D / y)) ≤
        408.3334 * T ^ 2 * (2 * L + 5.0122) + 1.01 * ((65.2667 * L + 297.266) * T ^ 2 +
          (16.037 * L + 76.63)) := by nlinarith
    have h0 : 0 ≤ D * Real.log (D / rexp 1) + (1 + 0.01) * Y *
        (√(3 + 2 * 0.01) * Real.log (5 * D) + 1 / 2 + (2 + Real.log D / 2) * logPlus (2 * D / y)) := by
      nlinarith
    have h2 := mul_le_mul hA h1 h0 (by norm_num)
    have h3 : 1.01 * (16.037 * L + 76.63) ≤ 0.001 * L * T ^ 2 + 0.001 * T ^ 2 := by
      have hT2 : 3.6e13 ≤ T ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hT2 hL0]
    nlinarith [sq_nonneg T, mul_nonneg hL0 (sq_nonneg T)]
  -- the `x/Q₀` term.
  have tB : 3 * c₁ / 2 * (2 * Real.log (5 * D) + (1 + 0.01) / 0.01 * Real.log D *
      logPlus (2 * D / y)) * (T ^ 3 / Q2 T) ≤ (0.2219 * L + 0.6671) * T ^ 2 := by
    have hxQ : T ^ 3 / Q2 T = 349 * T := by unfold Q2; field_simp
    rw [hxQ, hlp]
    have h1 : 2 * Real.log (5 * D) + (1 + 0.01) / 0.01 * Real.log D * Real.log (2 * D / y) ≤
        2 * (2 * L + 7.6217) + 101 * (2 * L + 6.0122) * 12.5604 := by
      have : Real.log D * Real.log (2 * D / y) ≤ (2 * L + 6.0122) * 12.5604 :=
        mul_le_mul hlD hlp1 hlp0 (by linarith)
      norm_num; nlinarith
    have h0 : 0 ≤ 2 * Real.log (5 * D) + (1 + 0.01) / 0.01 * Real.log D * Real.log (2 * D / y) := by
      positivity
    calc 3 * c₁ / 2 * (2 * Real.log (5 * D) + (1 + 0.01) / 0.01 * Real.log D * Real.log (2 * D / y)) *
          (349 * T)
        ≤ 3 * 1.000378 / 2 * (2 * (2 * L + 7.6217) + 101 * (2 * L + 6.0122) * 12.5604) * (349 * T) := by
          gcongr
      _ ≤ _ := by nlinarith [sq_nonneg T, mul_nonneg hL0 (sq_nonneg T)]
  -- the last term.
  have tC : 35 * c₀ * c₂ / (3 * π ^ 2) * q * Real.log D ≤ (0.1446 * L + 0.4346) * T ^ 2 := by
    have hk : 35 * c₀ * c₂ / (3 * π ^ 2) ≤ 25.22 := by
      have : c₀ = 32 := rfl
      rw [this, div_le_iff₀ (by positivity)]; nlinarith
    calc 35 * c₀ * c₂ / (3 * π ^ 2) * q * Real.log D ≤ 25.22 * (T ^ 2 / 349) * (2 * L + 6.0122) := by
          have : (0 : ℝ) < c₀ := by norm_num [c₀]
          gcongr
      _ ≤ _ := by
          rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
          nlinarith [sq_nonneg T, mul_nonneg hL0 (sq_nonneg T)]
  linarith [mul_nonneg hL0 (sq_nonneg T), sq_nonneg T]

/-- **`S_{I,2}` at the second parameters**: `≤ (0.031 L² + 3185.8 L + 8455.3) T²`. -/
theorem typeI2_second {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hc : SecondCase T δ q) :
    ‖typeI2 α (T ^ 3) (U2 T) (V2 T)‖ ≤
      (0.031 * Real.log T ^ 2 + 3185.8 * Real.log T + 8455.3) * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hL := fifteen_six_le_log hT
  have hL0 : 0 ≤ Real.log T := by linarith
  have hU' := U2_ge' hT
  have hV' := V2_ge' hT
  obtain ⟨hD1, -, -⟩ := D2_facts hT
  have key := lemma_4_2_4 h (two_e_le_Q2 hT) (by nlinarith) (by linarith) (by linarith)
    (by nlinarith) (U := U2 T) (V := V2 T)
  have h50 := b450_second hT h hc
  rcases le_or_gt |δ| (1 / (2 * c₂)) with hδ | hδ
  · -- `|δ| ≤ 1/2c₂`: necessarily case (a).
    have hca : T / 6 < q := by
      rcases hc with hc | ⟨-, hδ8, -⟩
      · exact hc
      · exfalso
        obtain ⟨hc2a, -⟩ := c₂_bounds
        have : 1 / (2 * c₂) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        linarith
    have h51 := b451_second hT hca h.2.2.2.2
    refine (key.1 (Or.inl hδ)).trans ?_
    nlinarith [mul_nonneg (sq_nonneg (Real.log T)) (sq_nonneg T), mul_nonneg hL0 (sq_nonneg T)]
  · have h52 := b452_second hT h hc hδ.le
    refine (key.2 hδ.le 0.01 (by norm_num) (by norm_num)).trans ?_
    nlinarith [mul_nonneg (sq_nonneg (Real.log T)) (sq_nonneg T), mul_nonneg hL0 (sq_nonneg T)]

/-- **Type I at the second parameters**: `|S_{I,1}| + |S_{I,2}| ≤ (0.0717 L² + 3199.9 L + 8471.0) T²`. -/
theorem typeI_second {α δ T : ℝ} {a : ℤ} {q : ℕ} (hT : 6e6 ≤ T)
    (h : Approx2 α (T ^ 3) δ a q (Q2 T)) (hc : SecondCase T δ q) :
    ‖typeILog α (T ^ 3) (U2 T)‖ + ‖typeI2 α (T ^ 3) (U2 T) (V2 T)‖ ≤
      (0.0717 * Real.log T ^ 2 + 3199.9 * Real.log T + 8471.0) * T ^ 2 := by
  have h1 := typeI1_second hT h hc
  have h2 := typeI2_second hT h hc
  have hL0 : 0 ≤ Real.log T := by linarith [fifteen_six_le_log hT]
  nlinarith [mul_nonneg (sq_nonneg (Real.log T)) (sq_nonneg T), mul_nonneg hL0 (sq_nonneg T), sq_nonneg T]

end TernaryGoldbach.MinorArcs
