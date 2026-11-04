import TernaryGoldbach.MajorArcs.Cor933

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.ButhePsi] [Fact TernaryGoldbach.RamareMoebius]

/-!
# [H, Cor 7.1.3] from [H, Cor 9.3.3] and Platt's verification

With `T₀ = 10⁸/q` (Platt, `platt_grh`) and `y ≥ 10⁸`, `q ≤ 3·10⁵`, `|δ| ≤ 4·3·10⁵/q`, the error term of
`cor_9_3_3` is at most `10⁻¹⁷ + 4.7·10⁶/(√q √y)` for `y ≥ 10²⁵` (for `q = 1`, [H]'s
`2.485·10⁻¹⁹ + (381500 + 76)/√y` ([H, §9.6]); for `q ≥ 2`, our constants).
-/

open Real MeasureTheory FourierTransform
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach (e Schar)
open TernaryGoldbach.MinorArcs (etaU)

/-- Taylor lower bound `∑_{i<n} xⁱ/i! ≤ eˣ`. -/
theorem exp_ge_taylor {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i / i.factorial ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx n

theorem exp_nat_ge (k : ℕ) : (2.7182818283 : ℝ) ^ k ≤ Real.exp k := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k

theorem exp_split_ge (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (2.7182818283 : ℝ) ^ k * ∑ i ∈ Finset.range n, u ^ i / i.factorial ≤ Real.exp (k + u) := by
  rw [Real.exp_add]
  exact mul_le_mul (exp_nat_ge k) (exp_ge_taylor hu n) (Finset.sum_nonneg fun i _ => by positivity)
    (Real.exp_pos _).le

theorem L_le : Real.log (1e8 / (2 * π)) ≤ 16.5829 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have hπ := Real.pi_gt_d6
  have h := exp_split_ge 16 (u := 0.5829) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  calc (1e8 : ℝ) / (2 * π) ≤ 1e8 / (2 * 3.141592) := by gcongr
    _ ≤ _ := by norm_num at h ⊢; linarith

theorem L_nonneg : 0 ≤ Real.log (1e8 / (2 * π)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  have := Real.pi_lt_d2; nlinarith

theorem exp_c_le : Real.exp (-(0.1598 * (1000 / 3))) ≤ 7.3551e-24 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have h := exp_split_ge 53 (u := 0.2666666) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  refine le_trans ?_ (h.trans (Real.exp_le_exp.2 (by norm_num)))
  norm_num

theorem log_1e8_le : Real.log 1e8 ≤ 18.421 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := exp_split_ge 18 (u := 0.421) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num at h ⊢; linarith

theorem log_3e5_le : Real.log 300000 ≤ 12.62 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := exp_split_ge 12 (u := 0.62) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num at h ⊢; linarith

/-- `t e^{-ct}` is decreasing for `t ≥ 1/c`. -/
theorem mul_exp_anti {c t₀ t : ℝ} (hc : 0 < c) (ht₀ : 1 ≤ c * t₀) (ht : t₀ ≤ t) :
    t * Real.exp (-(c * t)) ≤ t₀ * Real.exp (-(c * t₀)) := by
  have ht₀0 : 0 < t₀ := by
    by_contra h; push_neg at h; nlinarith
  have h1 : Real.exp (-(c * t)) = Real.exp (-(c * t₀)) * Real.exp (-(c * (t - t₀))) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : 1 + c * (t - t₀) ≤ Real.exp (c * (t - t₀)) := by
    have := Real.add_one_le_exp (c * (t - t₀)); linarith
  have h3 : t ≤ t₀ * (1 + c * (t - t₀)) := by nlinarith
  rw [h1]
  have hE : 0 < Real.exp (-(c * t₀)) := Real.exp_pos _
  have h4 : t * Real.exp (-(c * (t - t₀))) ≤ t₀ := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    calc t ≤ t₀ * (1 + c * (t - t₀)) := h3
      _ ≤ t₀ * Real.exp (c * (t - t₀)) := mul_le_mul_of_nonneg_left h2 ht₀0.le
  calc t * (Real.exp (-(c * t₀)) * Real.exp (-(c * (t - t₀))))
      = Real.exp (-(c * t₀)) * (t * Real.exp (-(c * (t - t₀)))) := by ring
    _ ≤ Real.exp (-(c * t₀)) * t₀ := mul_le_mul_of_nonneg_left h4 hE.le
    _ = t₀ * Real.exp (-(c * t₀)) := by ring

/-- The first line of the error term at `T₀ = 10⁸/q`. -/
theorem first_line_le {q : ℕ} (hq1 : 1 ≤ q) (hq3 : q ≤ 300000) {δ : ℝ}
    (hδ : |δ| ≤ 4 * 300000 / q) :
    (1e8 / q) * Real.log (q * (1e8 / q) / (2 * π)) *
      (6.11 * Real.exp (-0.1598 * (1e8 / q)) + 1.578 * expδ (1e8 / q) δ) ≤ 2.485e-19 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq3' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq3
  set T0 : ℝ := 1e8 / q with hT0
  have hqT : (q : ℝ) * T0 = 1e8 := by rw [hT0]; field_simp
  rw [hqT]
  have hL := L_le
  have hL0 := L_nonneg
  have hT1 : 1000 / 3 ≤ T0 := by rw [hT0, le_div_iff₀ hq0]; nlinarith
  have hT2 : T0 ≤ 1e8 := by rw [hT0, div_le_iff₀ hq0]; nlinarith
  -- the main part
  have hm := mul_exp_anti (c := 0.1598) (t₀ := 1000 / 3) (t := T0) (by norm_num) (by norm_num) hT1
  have hc := exp_c_le
  have h1 : T0 * Real.exp (-0.1598 * T0) ≤ 1000 / 3 * 7.3551e-24 := by
    rw [show -0.1598 * T0 = -(0.1598 * T0) by ring]
    exact hm.trans (mul_le_mul_of_nonneg_left hc (by norm_num))
  -- the `δ` part
  have h2 : expδ T0 δ ≤ Real.exp (-74) := by
    unfold expδ
    split_ifs with hδ0
    · exact (Real.exp_pos _).le
    · rw [Real.exp_le_exp]
      have hd : |δ| ≤ 1.2e6 / q := by linarith [show (4 * 300000 / q : ℝ) = 1.2e6 / q by ring]
      have hdpos : 0 < |δ| := abs_pos.2 hδ0
      have hπ := Real.pi_lt_d4
      have hπ0 := Real.pi_pos
      -- `(πδ)² ≤ (π · 1.2e6/q)² ≤ T0²/700`
      have hpd : (π * δ) ^ 2 ≤ T0 ^ 2 / 700 := by
        have e1 : (π * δ) ^ 2 = (π * |δ|) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
        rw [e1]
        have h3 : π * |δ| ≤ 3.1416 * (1.2e6 / q) := mul_le_mul hπ.le hd (abs_nonneg _) (by norm_num)
        have h4 : (3.1416 * (1.2e6 / q)) ^ 2 ≤ T0 ^ 2 / 700 := by
          rw [hT0, div_pow, mul_pow, div_pow]
          rw [le_div_iff₀ (by norm_num)]
          rw [show (3.1416 : ℝ) ^ 2 * (1.2e6 ^ 2 / (q : ℝ) ^ 2) * 700 =
            (3.1416 ^ 2 * 1.2e6 ^ 2 * 700) / (q : ℝ) ^ 2 by ring]
          exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
        exact (pow_le_pow_left₀ (by positivity) h3 2).trans h4
      have hpos : 0 < (π * δ) ^ 2 := by positivity
      have : 700 ≤ T0 ^ 2 / (π * δ) ^ 2 := by
        rw [le_div_iff₀ hpos]; rw [le_div_iff₀ (by norm_num)] at hpd; linarith
      rw [neg_mul, neg_div, neg_le_neg_iff, mul_div_assoc]
      linarith
  have h74 : Real.exp (-74) ≤ 1e-32 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := exp_nat_ge 74
    norm_num at this ⊢; linarith
  have hδ0 := expδ_nonneg T0 δ
  have hT0n : 0 ≤ T0 := by linarith
  calc T0 * Real.log (1e8 / (2 * π)) * (6.11 * Real.exp (-0.1598 * T0) + 1.578 * expδ T0 δ)
      = 6.11 * Real.log (1e8 / (2 * π)) * (T0 * Real.exp (-0.1598 * T0)) +
        1.578 * Real.log (1e8 / (2 * π)) * (T0 * expδ T0 δ) := by ring
    _ ≤ 6.11 * 16.5829 * (1000 / 3 * 7.3551e-24) + 1.578 * 16.5829 * (1e8 * 1e-32) := by
        gcongr
        exact h2.trans h74
    _ ≤ 2.485e-19 := by norm_num


set_option maxHeartbeats 1000000 in
/-- [H]'s error term at `T₀ = 10⁸/q`: `err933 ≤ 2.485·10⁻¹⁹ + (381500/√q + 76)/√y` ([H, §9.6]). -/
theorem err933_le_book {y : ℝ} (hy : 1e8 ≤ y) {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ 300000) {δ : ℝ}
    (hδ : |δ| ≤ 4 * 300000 / q) :
    err933 q (1e8 / q) δ y ≤ 2.485e-19 + (381500 / √q + 76) / √y := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq3' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hd : |δ| ≤ 1.2e6 / q := by linarith [show (4 * 300000 / q : ℝ) = 1.2e6 / q by ring]
  have hfirst := first_line_le hq1 hq hδ
  -- notation
  set t := √y with ht_def
  set s := √(q : ℝ) with hs_def
  have ht : 1e4 ≤ t := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have ht0 : 0 < t := by linarith
  have hyt : y = t * t := (Real.mul_self_sqrt (by linarith)).symm
  have hs1 : 1 ≤ s := by rw [hs_def]; exact Real.one_le_sqrt.2 hq1'
  have hs0 : 0 < s := by linarith
  have hss : s * s = q := Real.mul_self_sqrt hq0.le
  have hsq : s ≤ q := by
    calc s = s * 1 := (mul_one s).symm
      _ ≤ s * s := mul_le_mul_of_nonneg_left hs1 hs0.le
      _ = q := hss
  have hsT : √(1e8 / (q : ℝ)) = 1e4 / s := by
    rw [Real.sqrt_div (by norm_num), show (1e8 : ℝ) = 1e4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hqT : (q : ℝ) * (1e8 / q) = 1e8 := by field_simp
  have hL8 := log_1e8_le
  have hlq : Real.log q ≤ 12.62 := (Real.log_le_log hq0 hq3').trans log_3e5_le
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1'
  have hL80 : 0 ≤ Real.log 1e8 := Real.log_nonneg (by norm_num)
  set u := 1 / t with hu
  set v := 1 / s with hv
  have hu0 : 0 < u := by positivity
  have hv0 : 0 < v := by positivity
  have hu4 : u ≤ 1e-4 := by rw [hu, div_le_iff₀ ht0]; linarith
  have hqv : 1 / (q : ℝ) ≤ v := one_div_le_one_div_of_le hs0 hsq
  have hδv : |δ| ≤ 1.2e6 * v := hd.trans (by
    rw [show (1.2e6 / q : ℝ) = 1.2e6 * (1 / q) by ring]; exact mul_le_mul_of_nonneg_left hqv (by norm_num))
  unfold err933
  rw [hsT, hqT, ← ht_def]
  rw [hqT] at hfirst
  -- the `1/√y` terms
  have hA : 1.37259 * (1.22 * (1e4 / s) * Real.log 1e8 + 5.056 * (1e4 / s) + 1.423 * Real.log q + 37.19) / t ≤
      377871 * (v * u) + 75.7 * u := by
    have e : 1.37259 * (1.22 * (1e4 / s) * Real.log 1e8 + 5.056 * (1e4 / s) + 1.423 * Real.log q + 37.19) / t =
        1.37259 * (1.22e4 * Real.log 1e8 + 5.056e4) * (v * u) + 1.37259 * (1.423 * Real.log q + 37.19) * u := by
      simp only [hu, hv]; field_simp; ring
    rw [e]
    have hvu : 0 ≤ v * u := by positivity
    have h1 : 1.37259 * (1.22e4 * Real.log 1e8 + 5.056e4) * (v * u) ≤ 377871 * (v * u) := by
      apply mul_le_mul_of_nonneg_right _ hvu; linarith
    have h2 : 1.37259 * (1.423 * Real.log q + 37.19) * u ≤ 75.7 * u := by
      apply mul_le_mul_of_nonneg_right _ hu0.le; linarith
    linarith
  have hB : (3 * 1.92182 + 11 * |δ|) / y ≤ 1322 * (v * u) + 0.0006 * u := by
    have e : (3 * 1.92182 + 11 * |δ|) / y = (3 * 1.92182 + 11 * |δ|) * u * u := by
      rw [hyt, hu]; field_simp
    rw [e]
    have h1 : (3 * 1.92182 + 11 * |δ|) * u ≤ 0.0006 + 1322 * v := by
      have : (3 * 1.92182 + 11 * |δ|) * u ≤ (3 * 1.92182 + 11 * (1.2e6 * v)) * 1e-4 :=
        mul_le_mul (by linarith) hu4 hu0.le (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_right h1 hu0.le
    linarith
  have hC : (Real.log q + 6) * (2.74517 + 6 * 1.37259 * |δ|) / (y * t) ≤ 2 * (v * u) + 0.000001 * u := by
    have e : (Real.log q + 6) * (2.74517 + 6 * 1.37259 * |δ|) / (y * t) =
        (Real.log q + 6) * (2.74517 + 6 * 1.37259 * |δ|) * (u * u) * u := by
      rw [hyt, hu]; field_simp
    rw [e]
    have huu : u * u ≤ 1e-8 := by
      calc u * u ≤ 1e-4 * 1e-4 := mul_le_mul hu4 hu4 hu0.le (by norm_num)
        _ = 1e-8 := by norm_num
    have h1 : (Real.log q + 6) * (2.74517 + 6 * 1.37259 * |δ|) * (u * u) ≤
        (12.62 + 6) * (2.74517 + 6 * 1.37259 * (1.2e6 * v)) * 1e-8 := by
      apply mul_le_mul _ huu (by positivity) (by positivity)
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    have h2 : (12.62 + 6) * (2.74517 + 6 * 1.37259 * (1.2e6 * v)) * 1e-8 ≤ 0.000001 + 2 * v := by
      linarith
    have := mul_le_mul_of_nonneg_right (h1.trans h2) hu0.le
    linarith
  have hfin : (381500 / s + 76) / t = 381500 * (v * u) + 76 * u := by
    simp only [hu, hv]; field_simp
  rw [hfin]
  have hvu : 0 ≤ v * u := by positivity
  linarith


/-! ## The error for `q ≥ 2` at `T₀ = 10⁸/q` -/

open TernaryGoldbach.Explicit (BP E0b E1b E2b Vb EA EB Z3 c3 ZL Jl rhoA rhoB thetaD DN)

theorem log_le_of_le_exp {x c : ℝ} (hx : 0 < x) (h : x ≤ Real.exp c) : Real.log x ≤ c :=
  (Real.log_le_iff_le_exp hx).2 h

theorem log1400_le : Real.log 1400 ≤ 7.2443 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 7 (u := 0.2443) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_107644_le : Real.log 1.07644e8 ≤ 18.4944 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 18 (u := 0.4944) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_104344_le : Real.log 1.04344e8 ≤ 18.4633 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 18 (u := 0.4633) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log125_le : Real.log 1.25 ≤ 0.22315 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 0 (u := 0.22315) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log34_le : Real.log (3 / 4) ≤ -0.2876 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := Real.exp_bound' (x := 0.2876) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  norm_num; linarith

theorem neg_log0355_le : -Real.log 0.355 ≤ 1.0357 := by
  rw [← Real.log_inv]
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 1 (u := 0.0357) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log22_le : Real.log 22 ≤ 3.0911 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 3 (u := 0.0911) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log1375_le : Real.log 13.75 ≤ 2.6211 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 2 (u := 0.6211) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log300001_le : Real.log 300001 ≤ 12.62 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 12 (u := 0.62) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log512_le : Real.log 512 ≤ 6.2384 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 6 (u := 0.2384) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_ratio_23_ge : 1.4696 ≤ Real.log (10 / 2.3) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_bound' (x := 0.7348) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have e : Real.exp 1.4696 = Real.exp 0.7348 * Real.exp 0.7348 := by rw [← Real.exp_add]; norm_num
  rw [e]
  have h0 := Real.exp_pos 0.7348
  nlinarith

theorem log_ratio_3_ge : 1.2039 ≤ Real.log (10 / 3) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_bound' (x := 0.60195) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have e : Real.exp 1.2039 = Real.exp 0.60195 * Real.exp 0.60195 := by rw [← Real.exp_add]; norm_num
  rw [e]
  have h0 := Real.exp_pos 0.60195
  nlinarith

/-- `log(B'_{T₀+3.48}/0.355) ≤ 213.4` at `T₀ = 10⁸/q`, `2 ≤ q ≤ 3·10⁵`. -/
theorem logBP_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq3 : q ≤ 300000) :
    Real.log (BP q (1e8 / q + 3.48) / 0.355) ≤ 213.4 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2' : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hq3' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq3
  rw [Explicit.log_BP_eq]
  have hT : (0:ℝ) ≤ 1e8 / q + 3.48 := by positivity
  rw [abs_of_nonneg hT]
  have e1 : 1e8 / (q:ℝ) + 3.48 + 22 = (1e8 + 25.48 * q) / q := by field_simp; ring
  have e2 : 1.25 * (1e8 / (q:ℝ) + 3.48 + 11) = 1.25 * ((1e8 + 14.48 * q) / q) := by field_simp; ring
  rw [e1, e2, Real.log_div (by positivity) hq0.ne', Real.log_mul (by norm_num) (by positivity),
    Real.log_div (by positivity) hq0.ne']
  have h1 : Real.log (q + 1) - 2 * Real.log q ≤ -0.2876 := by
    have e : Real.log (q + 1) - 2 * Real.log q = Real.log ((q + 1) / q ^ 2) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow]; push_cast; ring
    rw [e]
    have h34 : ((q:ℝ) + 1) / q ^ 2 ≤ 3 / 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    exact (Real.log_le_log (by positivity) h34).trans log34_le
  have h2 : Real.log (1e8 + 25.48 * q) ≤ 18.4944 :=
    (Real.log_le_log (by positivity) (by linarith)).trans log_107644_le
  have h3 : Real.log (1e8 + 14.48 * q) ≤ 18.4633 :=
    (Real.log_le_log (by positivity) (by linarith)).trans log_104344_le
  have := log1400_le
  have := log125_le
  have := neg_log0355_le
  linarith

theorem ZL_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq3 : q ≤ 300000) : ZL q (1e8 / q) ≤ 145.21 := by
  unfold ZL
  have h := logBP_le hq2 hq3
  have hl := log_ratio_23_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.log_BP_pos q (1e8 / q + 3.48)]

theorem Z3_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq3 : q ≤ 300000) : Z3 q (1e8 / q) ≤ 177.26 := by
  unfold Z3
  have hm : Real.log (BP q (1e8 / q) / 0.355) ≤ Real.log (BP q (1e8 / q + 3.48) / 0.355) := by
    apply Explicit.log_BP_mono
    have : (0:ℝ) ≤ 1e8 / q := by positivity
    rw [abs_of_nonneg this, abs_of_nonneg (by positivity)]; linarith
  have h := (hm.trans (logBP_le hq2 hq3))
  have hl := log_ratio_3_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.log_BP_pos q (1e8 / q)]

/-- `E₁ ≤ 3.42·10⁶/√q` at `T₀ = 10⁸/q`. -/
theorem E1b_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq3 : q ≤ 300000) :
    E1b q (1e8 / q) ≤ 3.42e6 / √q := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq3' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq3
  have hs0 : 0 < √(q:ℝ) := Real.sqrt_pos.2 hq0
  set A := (Jl (1e8 / q) : ℝ) * 3.48 with hA
  have hA1 : A ≤ 1e8 / q + 3.48 := by
    rw [hA]; unfold Jl; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 1e8 / q / 3.48 by positivity)
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  have hA2 : A ≤ 1.010467e8 / q := by
    refine hA1.trans ?_
    rw [div_add' _ _ _ hq0.ne', div_le_div_iff_of_pos_right hq0]; linarith
  have hA0 : 0 ≤ A := by positivity
  have hpi := Real.pi_lt_d4
  have hsq : ∀ c K : ℝ, 0 ≤ c → 0 < K → 2 * 3.1416 * c * 2 * 1.010467e8 ≤ K ^ 2 →
      √(2 * π * c * (2 * A)) ≤ K / √q := by
    intro c K hc hK h
    have h1 : 2 * π * c * (2 * A) ≤ K ^ 2 / q := by
      calc 2 * π * c * (2 * A) ≤ 2 * 3.1416 * c * (2 * (1.010467e8 / q)) := by gcongr
        _ = (2 * 3.1416 * c * 2 * 1.010467e8) / q := by ring
        _ ≤ K ^ 2 / q := div_le_div_of_nonneg_right h hq0.le
    calc √(2 * π * c * (2 * A)) ≤ √(K ^ 2 / q) := Real.sqrt_le_sqrt h1
      _ = K / √q := by rw [Real.sqrt_div' _ hq0.le, Real.sqrt_sq hK.le]
  have h1 := hsq 0.6647 29053 (by norm_num) (by norm_num) (by norm_num)
  have h2 := hsq 0.1707 14723 (by norm_num) (by norm_num) (by norm_num)
  have hZ := ZL_le hq2 hq3
  have hZ0 := Explicit.ZL_nonneg q (1e8 / q)
  unfold E1b
  rw [← hA]
  have hX : (1 / 3.48) * √(2 * π * 0.6647 * (2 * A)) + √(2 * π * 0.1707 * (2 * A)) ≤
      23071.6 / √q := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 1 / 3.48)
    have e : (1 / 3.48) * (29053 / √q) + 14723 / √q = (29053 / 3.48 + 14723) / √q := by
      field_simp
    have h3 : (29053 / 3.48 + 14723 : ℝ) / √q ≤ 23071.6 / √q :=
      div_le_div_of_nonneg_right (by norm_num) hs0.le
    linarith
  have hX0 : 0 ≤ (1 / 3.48) * √(2 * π * 0.6647 * (2 * A)) + √(2 * π * 0.1707 * (2 * A)) := by
    positivity
  calc ZL q (1e8 / q) * ((1 / 3.48) * √(2 * π * 0.6647 * (2 * A)) + √(2 * π * 0.1707 * (2 * A)))
      ≤ 145.21 * (23071.6 / √q) := mul_le_mul hZ hX hX0 (by norm_num)
    _ ≤ 3.42e6 / √q := by
        rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by norm_num) hs0.le

theorem rhoB_le : rhoB ≤ 0.5406 := by
  unfold rhoB
  have h := exp_split_ge 0 (u := 0.61512) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num; linarith

theorem exp_neg74_le : Real.exp (-74) ≤ 1e-32 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := exp_nat_ge 74
  norm_num at this ⊢; linarith

/-- `E₂ ≤ 2·10⁻¹⁸` at `T₀ = 10⁸/q`, `|δ| ≤ 1.2·10⁶/q`. -/
theorem E2b_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq3 : q ≤ 300000) {δ : ℝ}
    (hδ : |δ| ≤ 1.2e6 / q) : E2b q (1e8 / q) δ ≤ 2e-18 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2' : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hq3' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq3
  set T0 : ℝ := 1e8 / q with hT0
  have hT1 : 1000 / 3 ≤ T0 := by rw [hT0, le_div_iff₀ hq0]; nlinarith
  have hpi := Real.pi_lt_d4
  have hpi' := Real.pi_gt_three
  -- `E_B`
  have hEB : EB T0 ≤ 0.892 * (1000 / 3 * 7.3551e-24) := by
    unfold EB
    have hm := mul_exp_anti (c := 0.1598) (t₀ := 1000 / 3) (t := T0) (by norm_num) (by norm_num) hT1
    rw [show -0.1598 * T0 = -(0.1598 * T0) by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left exp_c_le (by norm_num)))
      (by norm_num)
  have hEB0 := Explicit.EB_nonneg (by linarith : (0:ℝ) ≤ T0)
  -- `E_A`
  have hEA : EA T0 δ ≤ 4.13e-30 := by
    unfold EA
    split_ifs with hδ0
    · norm_num
    · have hd : 0 < |δ| := abs_pos.2 hδ0
      have hu : 26.5 ≤ T0 / (π * |δ|) := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : π * |δ| ≤ 3.1416 * (1.2e6 / q) := mul_le_mul hpi.le hδ (abs_nonneg _) (by norm_num)
        have h2 : 26.5 * (3.1416 * (1.2e6 / q)) ≤ T0 := by
          rw [hT0, show (26.5 : ℝ) * (3.1416 * (1.2e6 / q)) = (26.5 * 3.1416 * 1.2e6) / q by ring]
          exact div_le_div_of_nonneg_right (by norm_num) hq0.le
        nlinarith
      have hg := Explicit.gauss_sq_anti (by norm_num : (10:ℝ) ≤ 26.5) hu
      have he : Real.exp (-0.1065 * (26.5:ℝ) ^ 2) ≤ 1e-32 :=
        (Real.exp_le_exp.2 (by norm_num)).trans exp_neg74_le
      calc 0.588 * (T0 / (π * |δ|)) ^ 2 * Real.exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)
          = 0.588 * ((T0 / (π * |δ|)) ^ 2 * Real.exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)) := by ring
        _ ≤ 0.588 * ((26.5:ℝ) ^ 2 * Real.exp (-0.1065 * (26.5:ℝ) ^ 2)) := by gcongr
        _ ≤ 0.588 * ((26.5:ℝ) ^ 2 * 1e-32) := by gcongr
        _ ≤ 4.13e-30 := by norm_num
  have hEA0 := Explicit.EA_nonneg T0 δ
  -- the counts
  have hZ := Z3_le hq2 hq3
  rw [← hT0] at hZ
  have hZ0 := Explicit.Z3_nonneg q T0
  have hc : c3 T0 ≤ 0.12061 := by
    unfold c3
    have hl := log_ratio_3_ge
    rw [div_div, div_le_iff₀ (by positivity)]
    have : 11 * 4.4 ≤ 0.12061 * (T0 * 1.2039) := by nlinarith
    nlinarith
  have hc0 := Explicit.c3_nonneg (by linarith : (0:ℝ) < T0)
  -- the geometric factors
  have hB := rhoB_le
  have hB1 : 1 / (1 - rhoB) ≤ 2.1768 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hB0 : 0 ≤ 1 / (1 - rhoB) := by rw [one_div]; exact inv_nonneg.2 (by linarith)
  have hA1 : 1 / (1 - rhoA δ) ≤ 2.22e5 := by
    unfold rhoA
    refine (Explicit.inv_one_sub_exp_neg_le (by positivity)).trans ?_
    have hd6 : |δ| ≤ 6e5 := hδ.trans (by rw [div_le_iff₀ hq0]; nlinarith)
    rw [one_div_div]
    have : π * (|δ| + 1) / (1.93 * 4.4) ≤ 3.1416 * (6e5 + 1) / (1.93 * 4.4) :=
      div_le_div_of_nonneg_right (mul_le_mul hpi.le (by linarith) (by positivity) (by norm_num))
        (by norm_num)
    have h2 : 3.1416 * (6e5 + 1) / (1.93 * 4.4) ≤ (2.22e5 - 1 : ℝ) := by norm_num
    linarith
  have hA0 : 0 ≤ 1 / (1 - rhoA δ) := by
    have := Explicit.rhoA_lt_one δ; rw [one_div]; exact inv_nonneg.2 (by linarith)
  unfold E2b
  rw [div_eq_mul_one_div (2 * Z3 q T0) (1 - rhoB), div_eq_mul_one_div (2 * c3 T0) ((1 - rhoB) ^ 2),
    div_eq_mul_one_div (2 * Z3 q T0) (1 - rhoA δ), div_eq_mul_one_div (2 * c3 T0) ((1 - rhoA δ) ^ 2),
    ← one_div_pow, ← one_div_pow]
  have hX : 2 * Z3 q T0 * (1 / (1 - rhoB)) + 2 * c3 T0 * (1 / (1 - rhoB)) ^ 2 ≤
      2 * 177.26 * 2.1768 + 2 * 0.12061 * 2.1768 ^ 2 := by
    have := pow_le_pow_left₀ hB0 hB1 2
    gcongr
  have hY : 2 * Z3 q T0 * (1 / (1 - rhoA δ)) + 2 * c3 T0 * (1 / (1 - rhoA δ)) ^ 2 ≤
      2 * 177.26 * 2.22e5 + 2 * 0.12061 * (2.22e5) ^ 2 := by
    have := pow_le_pow_left₀ hA0 hA1 2
    gcongr
  have hX0 : 0 ≤ 2 * Z3 q T0 * (1 / (1 - rhoB)) + 2 * c3 T0 * (1 / (1 - rhoB)) ^ 2 := by positivity
  have hY0 : 0 ≤ 2 * Z3 q T0 * (1 / (1 - rhoA δ)) + 2 * c3 T0 * (1 / (1 - rhoA δ)) ^ 2 := by
    positivity
  have h1 := mul_le_mul hEB hX hX0 (by norm_num)
  have h2 := mul_le_mul hEA hY hY0 (by norm_num)
  norm_num at h1 h2 ⊢
  linarith

/-- `E₀ ≤ 15300` for `q ≤ 3·10⁵`. -/
theorem E0b_le {q : ℕ} [NeZero q] (hq3 : q ≤ 300000) : E0b q ≤ 15300 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq3' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq3
  unfold E0b
  rw [Explicit.log_BP_eq, abs_zero, zero_add, zero_add, show (1.25 : ℝ) * 11 = 13.75 by norm_num]
  have hl1 : Real.log q ≤ 12.62 := (Real.log_le_log hq0 hq3').trans log_3e5_le
  have hl2 : Real.log (q + 1) ≤ 12.62 :=
    (Real.log_le_log (by positivity) (by linarith)).trans log300001_le
  have := log1400_le
  have := log22_le
  have := log1375_le
  have := neg_log0355_le
  have hl := log_ratio_3_ge
  have hS : Real.log 1400 + 9 * Real.log q + Real.log (q + 1) + Real.log 22 + 10 * Real.log 13.75 -
      Real.log 0.355 ≤ 163.79 := by linarith
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith [Explicit.log_BP_pos q 0]

/-- `V ≤ 2.1·10¹⁶` for `2 ≤ q ≤ 3·10⁵`, `|δ| ≤ 1.2·10⁶/q`. -/
theorem Vb_le {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq3 : q ≤ 300000) {δ : ℝ}
    (hδ : |δ| ≤ 1.2e6 / q) : Vb q δ ≤ 2.1e16 := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2' : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hq3' : (q:ℝ) ≤ 300000 := by exact_mod_cast hq3
  have hd6 : |δ| ≤ 6e5 := hδ.trans (by rw [div_le_iff₀ hq0]; nlinarith)
  have hθ1 : 2 / thetaD δ ≤ 4.2858e6 := by
    unfold thetaD; rw [div_div_eq_mul_div, div_le_iff₀ (by norm_num)]; nlinarith
  have hθ2 : 2 / thetaD δ ^ 2 ≤ 9.1838e12 := by
    unfold thetaD; rw [div_pow, div_div_eq_mul_div, div_le_iff₀ (by norm_num)]
    have : (1 + |δ|) ^ 2 ≤ (1 + 6e5) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  have hDN : DN q ≤ 133.48 := by
    unfold DN
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have hl1 : Real.log q ≤ 12.62 := (Real.log_le_log hq0 hq3').trans log_3e5_le
    have hl2 : Real.log (q + 1) ≤ 12.62 :=
      (Real.log_le_log (by positivity) (by linarith)).trans log300001_le
    have := log512_le
    have := neg_log0355_le
    push_cast; linarith
  have hl2 : 2 / Real.log 2 + 4.8 ≤ 7.6855 := by
    have := Real.log_two_gt_d9
    rw [← le_sub_iff_add_le, div_le_iff₀ (by linarith)]; nlinarith
  have hD0 := Explicit.DN_nonneg q
  have hθ0 := Explicit.thetaD_pos δ
  unfold Vb
  have hX : (DN q + 37) * (2 / thetaD δ) + 2.6 * (2 / thetaD δ ^ 2) ≤
      (133.48 + 37) * 4.2858e6 + 2.6 * 9.1838e12 := by gcongr
  have hX0 : 0 ≤ (DN q + 37) * (2 / thetaD δ) + 2.6 * (2 / thetaD δ ^ 2) := by positivity
  have hl0 : 0 ≤ 2 / Real.log 2 + 4.8 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  calc 112 * (2 / Real.log 2 + 4.8) * ((DN q + 37) * (2 / thetaD δ) + 2.6 * (2 / thetaD δ ^ 2))
      ≤ 112 * 7.6855 * ((133.48 + 37) * 4.2858e6 + 2.6 * 9.1838e12) := by gcongr
    _ ≤ 2.1e16 := by norm_num

/-- **The `q ≥ 2` error at `T₀ = 10⁸/q`**: `err933New ≤ 10⁻¹⁷ + 4.7·10⁶/(√q √y)` for `y ≥ 10²⁵`. -/
theorem err933New_le {y : ℝ} (hy : 1e25 ≤ y) {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq3 : q ≤ 300000)
    {δ : ℝ} (hδ : |δ| ≤ 1.2e6 / q) :
    err933New q (1e8 / q) δ y ≤ 1e-17 + 4.7e6 / √q / √y := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hy0 : 0 < y := by linarith
  have hsy : 3.16e12 ≤ √y := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq0 : 0 < √(q:ℝ) := Real.sqrt_pos.2 hq0
  have h2 := E2b_le hq2 hq3 hδ
  have h1 := E1b_le hq2 hq3
  have h0 := E0b_le (q := q) hq3
  have hV := Vb_le hq2 hq3 hδ
  have hpi := Real.pi_gt_three
  unfold err933New
  have t1 : 1.37259 * E1b q (1e8 / q) / √y ≤ 4.7e6 / √q / √y := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    calc 1.37259 * E1b q (1e8 / q) ≤ 1.37259 * (3.42e6 / √q) := by gcongr
      _ ≤ 4.7e6 / √q := by rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by norm_num) hsq0.le
  have t2 : 1.92182 * E0b q / y ≤ 1e-20 := by
    rw [div_le_iff₀ hy0]; nlinarith
  have t3 : 2.74517 * Vb q δ / (2 * π * (y * √y)) ≤ 1e-20 := by
    rw [div_le_iff₀ (by positivity)]
    have : y * √y ≥ 1e25 * 3.16e12 := mul_le_mul hy hsy (by norm_num) hy0.le
    have hV0 := Explicit.Vb_nonneg q δ
    nlinarith
  linarith

/-! ## The error for `q = 1` (`ζ`) at `T₀ = 10⁸` -/

open TernaryGoldbach.Explicit (BPz2 E1g E2g Z3g ZLg c3g Vz)

theorem log9201_le : Real.log 9201 ≤ 9.2 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 9 (u := 0.2) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_1e8p_le : Real.log (1e8 + 25.48) ≤ 18.43 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 18 (u := 0.43) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_125e8p_le : Real.log (1.25 * (1e8 + 14.48)) ≤ 18.65 := by
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_split_ge 18 (u := 0.65) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_BPz2_le : Real.log (BPz2 (1e8 + 3.48) / 0.355) ≤ 200 := by
  have hT : BPz2 (1e8 + 3.48) ≤ 9201 * (1e8 + 25.48) * (1.25 * (1e8 + 14.48)) ^ 9 := by
    unfold BPz2
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1e8 + 3.48)]
    norm_num
  have hpos : (0:ℝ) < 9201 * (1e8 + 25.48) * (1.25 * (1e8 + 14.48)) ^ 9 := by positivity
  have hB0 : 0 < BPz2 (1e8 + 3.48) := by unfold BPz2; positivity
  refine (Real.log_le_log (div_pos hB0 (by norm_num)) (div_le_div_of_nonneg_right hT (by norm_num))).trans ?_
  rw [Real.log_div hpos.ne' (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have := log9201_le
  have := log_1e8p_le
  have := log_125e8p_le
  have := neg_log0355_le
  push_cast
  linarith

theorem log_BPz2_zero_le : Real.log (BPz2 0 / 0.355) ≤ 40 := by
  have hv : BPz2 0 = 9200 * 22 * (1.25 * 11) ^ 9 + 20 * 22 ^ 3 * (1.25 * 11) ^ 2 := by
    unfold BPz2; norm_num
  rw [hv]
  refine log_le_of_le_exp (by norm_num) ?_
  have h := exp_nat_ge 40
  norm_num at h ⊢; linarith

theorem ZLz_le : ZLg BPz2 1e8 ≤ 136.1 := by
  unfold ZLg
  have h := log_BPz2_le
  have hl := log_ratio_23_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.polyDatum_zeta2.log_pos (1e8 + 3.48)]

theorem Z3z_le : Z3g BPz2 1e8 ≤ 166.2 := by
  unfold Z3g
  have hm : Real.log (BPz2 1e8 / 0.355) ≤ Real.log (BPz2 (1e8 + 3.48) / 0.355) :=
    Explicit.polyDatum_zeta2.log_mono (by rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]; norm_num)
  have h := hm.trans log_BPz2_le
  have hl := log_ratio_3_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.polyDatum_zeta2.log_pos 1e8]

theorem E1z_le : E1g BPz2 1e8 (2 * π * 0.6647) (2 * π * 0.1707) ≤ 3.42e6 := by
  set A := (Explicit.Jl 1e8 : ℝ) * 3.48 with hA
  have hA1 : A ≤ 1e8 + 3.48 := by
    rw [hA]; unfold Explicit.Jl; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 1e8 / 3.48 by positivity)
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  have hA0 : 0 ≤ A := by positivity
  have hpi := Real.pi_lt_d4
  have h1 : √(2 * π * 0.6647 * (2 * A)) ≤ 28902 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_pos]
  have h2 : √(2 * π * 0.1707 * (2 * A)) ≤ 14647 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_pos]
  have hZ := ZLz_le
  have hZ0 : 0 ≤ ZLg BPz2 1e8 :=
    div_nonneg (Explicit.polyDatum_zeta2.log_pos _).le (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le
  unfold E1g
  rw [← hA]
  have hX : (1 / 3.48) * √(2 * π * 0.6647 * (2 * A)) + √(2 * π * 0.1707 * (2 * A)) ≤ 22952.3 := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 1 / 3.48)
    norm_num at this ⊢; linarith
  have hX0 : 0 ≤ (1 / 3.48) * √(2 * π * 0.6647 * (2 * A)) + √(2 * π * 0.1707 * (2 * A)) := by positivity
  calc ZLg BPz2 1e8 * ((1 / 3.48) * √(2 * π * 0.6647 * (2 * A)) + √(2 * π * 0.1707 * (2 * A)))
      ≤ 136.1 * 22952.3 := mul_le_mul hZ hX hX0 (by norm_num)
    _ ≤ 3.42e6 := by norm_num

theorem E2z_le {δ : ℝ} (hδ : |δ| ≤ 1.2e6) :
    E2g BPz2 10 1e8 (EB 1e8) (EA 1e8 δ) rhoB (rhoA δ) ≤ 2e-18 := by
  have hpi := Real.pi_lt_d4
  have hpi' := Real.pi_gt_three
  have hEB : EB 1e8 ≤ 0.892 * (1000 / 3 * 7.3551e-24) := by
    unfold EB
    have hm := mul_exp_anti (c := 0.1598) (t₀ := 1000 / 3) (t := 1e8) (by norm_num) (by norm_num)
      (by norm_num)
    rw [show -0.1598 * (1e8 : ℝ) = -(0.1598 * 1e8) by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left exp_c_le (by norm_num)))
      (by norm_num)
  have hEB0 := Explicit.EB_nonneg (by norm_num : (0:ℝ) ≤ 1e8)
  have hEA : EA 1e8 δ ≤ 4.13e-30 := by
    unfold EA
    split_ifs with hδ0
    · norm_num
    · have hd : 0 < |δ| := abs_pos.2 hδ0
      have hu : 26.5 ≤ 1e8 / (π * |δ|) := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : π * |δ| ≤ 3.1416 * 1.2e6 := mul_le_mul hpi.le hδ (abs_nonneg _) (by norm_num)
        nlinarith
      have hg := Explicit.gauss_sq_anti (by norm_num : (10:ℝ) ≤ 26.5) hu
      have he : Real.exp (-0.1065 * (26.5:ℝ) ^ 2) ≤ 1e-32 :=
        (Real.exp_le_exp.2 (by norm_num)).trans exp_neg74_le
      calc 0.588 * (1e8 / (π * |δ|)) ^ 2 * Real.exp (-0.1065 * (1e8 / (π * |δ|)) ^ 2)
          = 0.588 * ((1e8 / (π * |δ|)) ^ 2 * Real.exp (-0.1065 * (1e8 / (π * |δ|)) ^ 2)) := by ring
        _ ≤ 0.588 * ((26.5:ℝ) ^ 2 * Real.exp (-0.1065 * (26.5:ℝ) ^ 2)) := by gcongr
        _ ≤ 0.588 * ((26.5:ℝ) ^ 2 * 1e-32) := by gcongr
        _ ≤ 4.13e-30 := by norm_num
  have hEA0 := Explicit.EA_nonneg 1e8 δ
  have hZ := Z3z_le
  have hZ0 : 0 ≤ Z3g BPz2 1e8 :=
    div_nonneg (Explicit.polyDatum_zeta2.log_pos _).le (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le
  have hc : c3g 10 1e8 ≤ 3.66e-7 := by
    unfold c3g
    have hl := log_ratio_3_ge
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hc0 : 0 ≤ c3g 10 1e8 :=
    div_nonneg (by norm_num) (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le
  have hB := rhoB_le
  have hB1 : 1 / (1 - rhoB) ≤ 2.1768 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hB0 : 0 ≤ 1 / (1 - rhoB) := by rw [one_div]; exact inv_nonneg.2 (by linarith)
  have hA1 : 1 / (1 - rhoA δ) ≤ 4.44e5 := by
    unfold rhoA
    refine (Explicit.inv_one_sub_exp_neg_le (by positivity)).trans ?_
    rw [one_div_div]
    have : π * (|δ| + 1) / (1.93 * 4.4) ≤ 3.1416 * (1.2e6 + 1) / (1.93 * 4.4) :=
      div_le_div_of_nonneg_right (mul_le_mul hpi.le (by linarith) (by positivity) (by norm_num))
        (by norm_num)
    have h2 : 3.1416 * (1.2e6 + 1) / (1.93 * 4.4) ≤ (4.44e5 - 1 : ℝ) := by norm_num
    linarith
  have hA0 : 0 ≤ 1 / (1 - rhoA δ) := by
    have := Explicit.rhoA_lt_one δ; rw [one_div]; exact inv_nonneg.2 (by linarith)
  unfold E2g
  rw [div_eq_mul_one_div (2 * Z3g BPz2 1e8) (1 - rhoB), div_eq_mul_one_div (2 * c3g 10 1e8) ((1 - rhoB) ^ 2),
    div_eq_mul_one_div (2 * Z3g BPz2 1e8) (1 - rhoA δ),
    div_eq_mul_one_div (2 * c3g 10 1e8) ((1 - rhoA δ) ^ 2), ← one_div_pow, ← one_div_pow]
  have hX : 2 * Z3g BPz2 1e8 * (1 / (1 - rhoB)) + 2 * c3g 10 1e8 * (1 / (1 - rhoB)) ^ 2 ≤
      2 * 166.2 * 2.1768 + 2 * 3.66e-7 * 2.1768 ^ 2 := by
    have := pow_le_pow_left₀ hB0 hB1 2
    gcongr
  have hY : 2 * Z3g BPz2 1e8 * (1 / (1 - rhoA δ)) + 2 * c3g 10 1e8 * (1 / (1 - rhoA δ)) ^ 2 ≤
      2 * 166.2 * 4.44e5 + 2 * 3.66e-7 * (4.44e5) ^ 2 := by
    have := pow_le_pow_left₀ hA0 hA1 2
    gcongr
  have hX0 : 0 ≤ 2 * Z3g BPz2 1e8 * (1 / (1 - rhoB)) + 2 * c3g 10 1e8 * (1 / (1 - rhoB)) ^ 2 := by
    positivity
  have hY0 : 0 ≤ 2 * Z3g BPz2 1e8 * (1 / (1 - rhoA δ)) + 2 * c3g 10 1e8 * (1 / (1 - rhoA δ)) ^ 2 := by
    positivity
  have h1 := mul_le_mul hEB hX hX0 (by norm_num)
  have h2 := mul_le_mul hEA hY hY0 (by norm_num)
  norm_num at h1 h2 ⊢
  linarith

theorem Vz_le {δ : ℝ} (hδ : |δ| ≤ 1.2e6) : Vz δ ≤ 1e17 := by
  have hθ1 : 2 / thetaD δ ≤ 8.5715e6 := by
    unfold thetaD; rw [div_div_eq_mul_div, div_le_iff₀ (by norm_num)]; nlinarith
  have hθ2 : 2 / thetaD δ ^ 2 ≤ 3.6735e13 := by
    unfold thetaD; rw [div_pow, div_div_eq_mul_div, div_le_iff₀ (by norm_num)]
    have : (1 + |δ|) ^ 2 ≤ (1 + 1.2e6) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  have hl2 : 2 / Real.log 2 + 4.8 ≤ 7.6855 := by
    have := Real.log_two_gt_d9
    rw [← le_sub_iff_add_le, div_le_iff₀ (by linarith)]; nlinarith
  have hθ0 := Explicit.thetaD_pos δ
  unfold Vz
  have hl0 : 0 ≤ 2 / Real.log 2 + 4.8 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  calc 112 * (2 / Real.log 2 + 4.8) * (40 * (2 / thetaD δ) + 2.6 * (2 / thetaD δ ^ 2))
      ≤ 112 * 7.6855 * (40 * 8.5715e6 + 2.6 * 3.6735e13) := by gcongr
    _ ≤ 1e17 := by norm_num

/-- **The `q = 1` error at `T₀ = 10⁸`**: `err933Z ≤ 10⁻¹⁷ + 4.7·10⁶/√y` for `y ≥ 10²⁵`, `|δ| ≤ 1.2·10⁶`. -/
theorem err933Z_le {y : ℝ} (hy : 1e25 ≤ y) {δ : ℝ} (hδ : |δ| ≤ 1.2e6) :
    err933Z 1e8 δ y ≤ 1e-17 + 4.7e6 / √y := by
  have hy0 : 0 < y := by linarith
  have hsy : 3.16e12 ≤ √y := Real.le_sqrt_of_sq_le (by nlinarith)
  have h2 := E2z_le hδ
  have h1 := E1z_le
  have hV := Vz_le hδ
  have hZ0 : 112 * Z3g BPz2 0 ≤ 15300 := by
    unfold Z3g
    have h := log_BPz2_zero_le
    have hl := log_ratio_3_ge
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [Explicit.polyDatum_zeta2.log_pos 0]
  have hpi := Real.pi_gt_three
  unfold err933Z
  have t1 : 1.37259 * E1g BPz2 1e8 (2 * π * 0.6647) (2 * π * 0.1707) / √y ≤ 4.7e6 / √y := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    nlinarith
  have t2 : 1.92182 * (112 * Z3g BPz2 0) / y ≤ 1e-20 := by
    rw [div_le_iff₀ hy0]; nlinarith
  have t3 : 2.74517 * Vz δ / (2 * π * (y * √y)) ≤ 1e-20 := by
    rw [div_le_iff₀ (by positivity)]
    have : y * √y ≥ 1e25 * 3.16e12 := mul_le_mul hy hsy (by norm_num) hy0.le
    have hV0 := Explicit.Vz_nonneg δ
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **[H, Cor 7.1.3]** (with our constants for `q ≥ 2`): for `y ≥ 10²⁵`, `χ` primitive mod `q ≤ 3·10⁵`,
`|δ| ≤ 4·3·10⁵/q`, `Σ Λ(n) χ(n) e(δn/y) η_*(n/y) = [q = 1] η̂_*(-δ) y + E y` with
`|E| ≤ 10⁻¹⁷ + 4.7·10⁶/(√q √y)`. From [H, Cor 9.3.3] (`cor_9_3_3`) and Platt's verification (numerical
hypothesis), at `T₀ = 10⁸/q` (for `q = 1`, `ζ`: `err933Z_le`). -/
theorem cor_7_1_3' {y : ℝ} (hy : 1e25 ≤ y) {q : ℕ} [NeZero q] (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {δ : ℝ} (hδ : |δ| ≤ 4 * 300000 / q) :
    ‖Schar χ (fun n => ((Λ n * etaU (n / y) : ℝ) : ℂ)) (δ / y) -
        (if q = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * y else 0)‖ ≤
      (1e-17 + 4.7e6 / √q / √y) * y := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hd : |δ| ≤ 1.2e6 / q := by linarith [show (4 * 300000 / q : ℝ) = 1.2e6 / q by ring]
  have hT0 : max (10 * π * |δ|) 50 ≤ 1e8 / q := by
    refine max_le ?_ ?_
    · have hπ := Real.pi_lt_d4
      have h1 : 10 * π * |δ| ≤ 10 * 3.1416 * (1.2e6 / q) :=
        mul_le_mul (by linarith) hd (abs_nonneg _) (by norm_num)
      refine h1.trans ?_
      rw [show (10 * 3.1416 * (1.2e6 / q) : ℝ) = 3.76992e7 / q by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hq0.le
    · rw [le_div_iff₀ hq0]
      have : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
      linarith
  have h := cor_9_3_3 (x := y) (by linarith) δ χ hχ hT0 (platt_grh hq χ hχ)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  have hsy : 0 < √y := Real.sqrt_pos.2 (by linarith)
  unfold err933N
  split_ifs with h1
  · have hs : √(q : ℝ) = 1 := by rw [h1]; simp
    have hq1' : (q : ℝ) = 1 := by exact_mod_cast h1
    rw [hs, div_one, hq1', div_one]
    exact err933Z_le hy (by rw [hq1'] at hd; simpa using hd)
  · exact err933New_le hy (by omega) hq hd

end TernaryGoldbach.MajorArcs
