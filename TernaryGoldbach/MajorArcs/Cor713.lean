import TernaryGoldbach.MajorArcs.Cor933

/-!
# [B, Cor 7.1.3] from [B, Cor 9.3.3] and Platt's verification

With `T₀ = 10⁸/q` (Platt, `platt_grh`) and `y ≥ 10⁸`, `q ≤ 3·10⁵`, `|δ| ≤ 4·3·10⁵/q`, the error term of
`cor_9_3_3` is at most `2.485·10⁻¹⁹ + (381500/√q + 76)/√y` ([B, §9.6]).
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
/-- **[B, Cor 7.1.3]**, proved from [B, Prop 9.3.2] (cited) and Platt's verification (numerical axiom):
for `y ≥ 10⁸`, `χ` primitive mod `q ≤ 3·10⁵`, `|δ| ≤ 4·3·10⁵/q`,
`Σ Λ(n) χ(n) e(δn/y) η_*(n/y) = [q = 1] η̂_*(-δ) y + E y`, `|E| ≤ 2.485·10⁻¹⁹ + (381500/√q + 76)/√y`. -/
theorem cor_7_1_3' {y : ℝ} (hy : 1e8 ≤ y) {q : ℕ} [NeZero q] (hq : q ≤ 300000)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {δ : ℝ} (hδ : |δ| ≤ 4 * 300000 / q) :
    ‖Schar χ (fun n => ((Λ n * etaU (n / y) : ℝ) : ℂ)) (δ / y) -
        (if q = 1 then 𝓕 (fun u => (etaU u : ℂ)) (-δ) * y else 0)‖ ≤
      (2.485e-19 + (381500 / √q + 76) / √y) * y := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq3' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hd : |δ| ≤ 1.2e6 / q := by linarith [show (4 * 300000 / q : ℝ) = 1.2e6 / q by ring]
  have hT0 : max (10 * π * |δ|) 50 ≤ 1e8 / q := by
    refine max_le ?_ ?_
    · have hπ := Real.pi_lt_d4
      have h1 : 10 * π * |δ| ≤ 10 * 3.1416 * (1.2e6 / q) :=
        mul_le_mul (by linarith) hd (abs_nonneg _) (by norm_num)
      refine h1.trans ?_
      rw [show (10 * 3.1416 * (1.2e6 / q) : ℝ) = 3.76992e7 / q by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hq0.le
    · rw [le_div_iff₀ hq0]; linarith
  have h := cor_9_3_3 (x := y) (by linarith) δ χ hχ hT0 (platt_grh hq χ hχ)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
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

end TernaryGoldbach.MajorArcs
