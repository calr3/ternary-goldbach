import TernaryGoldbach.Explicit.PsiRange1

/-!
# `|ψ(x) − x| ≤ 0.2 x/log³x` for `x ≥ e^{35000}`

With `L = log x`, `ℓ = log L`: `K₀ = ℓ + 4`, `Γ = L⁴/5`, `δ = 5(ℓ + 5)/L⁴`, `y₀ = 10¹⁰`.
-/

open Complex Set Filter MeasureTheory
open scoped Real ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

theorem log_35000_le : Real.log 35000 ≤ 10.4632 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 10 (u := 0.4632) (by norm_num) 10
  have e : ((10 : ℕ) : ℝ) + 0.4632 = 10.4632 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `L = 35000 e^u`, `ℓ = log L ≤ 10.4632 + u`, `u ≥ 0`. -/
theorem asymp_split {L : ℝ} (hL : 35000 ≤ L) :
    ∃ u : ℝ, 0 ≤ u ∧ Real.log L ≤ 10.4632 + u ∧ 35000 * (1 + u + u ^ 2 / 2) ≤ L := by
  refine ⟨Real.log L - Real.log 35000, ?_, ?_, ?_⟩
  · have := Real.log_le_log (by norm_num) hL; linarith
  · have := log_35000_le; linarith
  · have hL0 : 0 < L := by linarith
    have h1 : L = 35000 * Real.exp (Real.log L - Real.log 35000) := by
      rw [Real.exp_sub, Real.exp_log hL0, Real.exp_log (by norm_num)]; field_simp
    have h2 := exp_ge_taylor' (show 0 ≤ Real.log L - Real.log 35000 by
      have := Real.log_le_log (by norm_num) hL; linarith) 3
    norm_num [Finset.sum_range_succ] at h2
    nlinarith

theorem asymp_ineq1 {L : ℝ} (hL : 35000 ≤ L) : 105 * (Real.log L + 5) ^ 2 ≤ L := by
  obtain ⟨u, hu0, hu1, hu2⟩ := asymp_split hL
  have hl0 : 0 ≤ Real.log L + 5 := by have := Real.log_nonneg (by linarith : (1:ℝ) ≤ L); linarith
  have : (Real.log L + 5) ^ 2 ≤ (15.4632 + u) ^ 2 := pow_le_pow_left₀ hl0 (by linarith) 2
  nlinarith

theorem asymp_ineq2 {L : ℝ} (hL : 35000 ≤ L) : 44 * Real.log L * (11 * Real.log L - 53) ≤ L := by
  obtain ⟨u, hu0, hu1, hu2⟩ := asymp_split hL
  have hl : 10.46 ≤ Real.log L := by
    have h := Real.log_le_log (by norm_num) hL
    have : (10.46 : ℝ) ≤ Real.log 35000 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h1 := Real.exp_one_lt_d9
      have h2 := Real.exp_bound' (x := 0.46) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h2
      have e : Real.exp 10.46 = Real.exp 1 ^ 10 * Real.exp 0.46 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      have h3 : Real.exp 1 ^ 10 ≤ 2.7182818286 ^ 10 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 10
      have h4 : 0 ≤ Real.exp 1 ^ 10 := by positivity
      nlinarith [Real.exp_pos 0.46]
    linarith
  have hA : 44 * Real.log L * (11 * Real.log L - 53) ≤ 44 * (10.4632 + u) * (11 * (10.4632 + u) - 53) := by
    have h1 : 0 ≤ 11 * Real.log L - 53 := by linarith
    have h2 : 11 * Real.log L - 53 ≤ 11 * (10.4632 + u) - 53 := by linarith
    have : 44 * Real.log L ≤ 44 * (10.4632 + u) := by linarith
    calc 44 * Real.log L * (11 * Real.log L - 53) ≤ 44 * (10.4632 + u) * (11 * Real.log L - 53) :=
          mul_le_mul_of_nonneg_right this h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)
  nlinarith

theorem exp_53_le : Real.exp 53 ≤ 1.05e23 := by
  have h1 := Real.exp_one_lt_d9
  have : Real.exp 53 = Real.exp 1 ^ 53 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 53 ≤ 2.7182818286 ^ 53 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 53
    _ ≤ 1.05e23 := by norm_num

theorem exp_neg_125_le : Real.exp (-12.5) ≤ 3.8e-6 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have h := exp_split_ge' 12 (u := 0.5) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

/-- `MidB ≤ 0.01/L³` with `Γ = L⁴/5`. -/
theorem MidB_asymp_le {a δ x : ℝ} (hx : Real.exp 35000 ≤ x) (hδa : δ ^ 2 / 2 + |a| ≤ 1e-6) :
    MidB a δ (Real.log x ^ 4 / 5) x ≤ 0.01 / Real.log x ^ 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set L := Real.log x with hLdef
  have hL : 35000 ≤ L := by rw [hLdef, Real.le_log_iff_exp_le hx0]; exact hx
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓdef
  have hℓ : 10.46 ≤ ℓ := by
    have h := Real.log_le_log (by norm_num) hL
    have : (10.46 : ℝ) ≤ Real.log 35000 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h1 := Real.exp_one_lt_d9
      have h2 := Real.exp_bound' (x := 0.46) (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at h2
      have e : Real.exp 10.46 = Real.exp 1 ^ 10 * Real.exp 0.46 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
      rw [e]
      have h3 : Real.exp 1 ^ 10 ≤ 2.7182818286 ^ 10 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 10
      nlinarith [Real.exp_pos 0.46, pow_pos (Real.exp_pos 1) 10]
    linarith
  have hL4 : (1.5e18 : ℝ) ≤ L ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  unfold MidB
  have he : Real.exp (δ ^ 2 / 2 + |a|) ≤ 1.00001 := by
    have h := exp_small_le (t := δ ^ 2 / 2 + |a|) (by positivity) (by linarith)
    linarith
  -- `log Γ ≤ 4ℓ`
  have hlΓ : Real.log (L ^ 4 / 5) ≤ 4 * ℓ := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
    have := Real.log_pos (by norm_num : (1:ℝ) < 5); push_cast; linarith
  have hlΓ0 : 0 < Real.log (L ^ 4 / 5) := Real.log_pos (by linarith)
  have hzf : Real.exp (-(L / (11 * Real.log (L ^ 4 / 5)))) ≤ 1.05e23 / L ^ 11 := by
    have h2 := asymp_ineq2 hL
    rw [← hℓdef] at h2
    have h3 : -(L / (11 * Real.log (L ^ 4 / 5))) ≤ 53 - 11 * ℓ := by
      have : L / (11 * Real.log (L ^ 4 / 5)) ≥ L / (44 * ℓ) := by
        apply div_le_div_of_nonneg_left hL0.le (by positivity); linarith
      have : L / (44 * ℓ) ≥ 11 * ℓ - 53 := by
        rw [ge_iff_le, le_div_iff₀ (by positivity)]; nlinarith
      linarith
    refine (Real.exp_le_exp.2 h3).trans ?_
    rw [Real.exp_sub, show (11 : ℝ) * ℓ = ((11 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hℓdef,
      Real.exp_log hL0]
    exact div_le_div_of_nonneg_right exp_53_le (by positivity)
  have hK : ((⌊(L ^ 4 / 5 - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1 ≤ L ^ 4 / 22 := by
    have := Nat.floor_le (show (0:ℝ) ≤ (L ^ 4 / 5 - 3e12) / 4.4 by
      apply div_nonneg _ (by norm_num); linarith)
    have : (L ^ 4 / 5 - 3e12) / 4.4 + 1 ≤ L ^ 4 / 22 := by
      rw [div_add_one (by norm_num), div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
    linarith
  have hZ := Z3g_H_le; have hZ0 := Z3g_H_nonneg
  have hc := c3g_H_le; have hc0 := c3g_H_nonneg
  have hK0 : (0:ℝ) ≤ ((⌊(L ^ 4 / 5 - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1 := by positivity
  have hin : 2 * Z3g BPz2 3e12 + 2 * c3g 10 3e12 * (((⌊(L ^ 4 / 5 - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1) ≤ 1.2e-12 * L ^ 4 := by
    have : 2 * c3g 10 3e12 * (((⌊(L ^ 4 / 5 - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1) ≤ 2 * 1.22e-11 * (L ^ 4 / 22) := by
      gcongr
    nlinarith
  have hzf0 : 0 ≤ Real.exp (-(L / (11 * Real.log (L ^ 4 / 5)))) := (Real.exp_pos _).le
  calc 2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e12 * Real.exp (-(L / (11 * Real.log (L ^ 4 / 5)))) *
        ((((⌊(L ^ 4 / 5 - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1) * (2 * Z3g BPz2 3e12 + 2 * c3g 10 3e12 *
          (((⌊(L ^ 4 / 5 - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1)))
      ≤ 2 * 1.00001 / 3e12 * (1.05e23 / L ^ 11) * (L ^ 4 / 22 * (1.2e-12 * L ^ 4)) := by
        gcongr
    _ = (2 * 1.00001 / 3e12 * 1.05e23 / 22 * 1.2e-12) / L ^ 3 := by
        field_simp
    _ ≤ 0.01 / L ^ 3 := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem log_log_ge {x : ℝ} (hx : Real.exp 35000 ≤ x) : 10.46 ≤ Real.log (Real.log x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 35000 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have h := Real.log_le_log (by norm_num) hL
  have : (10.46 : ℝ) ≤ Real.log 35000 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h1 := Real.exp_one_lt_d9
    have h2 := Real.exp_bound' (x := 0.46) (by norm_num) (by norm_num) (n := 8) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h2
    have e : Real.exp 10.46 = Real.exp 1 ^ 10 * Real.exp 0.46 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [e]
    have h3 : Real.exp 1 ^ 10 ≤ 2.7182818286 ^ 10 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 10
    nlinarith [Real.exp_pos 0.46, pow_pos (Real.exp_pos 1) 10]
  linarith

set_option maxHeartbeats 800000 in
/-- `TailBG ≤ 10⁻⁴/L³` with `Γ = L⁴/5`, `δ = 5(ℓ + 5)/L⁴`. -/
theorem TailBG_asymp_le {a x : ℝ} (hx : Real.exp 35000 ≤ x)
    (hδa : (5 * (Real.log (Real.log x) + 5) / Real.log x ^ 4) ^ 2 / 2 + |a| ≤ 1e-6) :
    TailBG a (5 * (Real.log (Real.log x) + 5) / Real.log x ^ 4) (Real.log x ^ 4 / 5) ≤
      1e-4 / Real.log x ^ 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hℓ := log_log_ge hx
  set L := Real.log x with hLdef
  have hL : 35000 ≤ L := by rw [hLdef, Real.le_log_iff_exp_le hx0]; exact hx
  have hL0 : 0 < L := by linarith
  set ℓ := Real.log L with hℓdef
  set Γ := L ^ 4 / 5 with hΓ
  set δ := 5 * (ℓ + 5) / L ^ 4 with hδ
  have hL4 : (1.5e18 : ℝ) ≤ L ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  have hΓ0 : 0 < Γ := by positivity
  have hδΓ : δ * Γ = ℓ + 5 := by rw [hδ, hΓ]; field_simp
  have h105 := asymp_ineq1 hL
  rw [← hℓdef] at h105
  unfold TailBG EBg rhoG
  set t := 4.4 * δ ^ 2 * Γ with ht
  have htΓ : t * Γ = 4.4 * (ℓ + 5) ^ 2 := by rw [ht, ← hδΓ]; ring
  have ht0 : 0 < t := by rw [ht]; have : 0 < δ := by rw [hδ]; positivity
                         positivity
  have ht1 : t ≤ 1 := by
    have : t = 4.4 * (ℓ + 5) ^ 2 / Γ := by rw [eq_div_iff hΓ0.ne']; exact htΓ
    rw [this, div_le_one hΓ0, hΓ]
    have h1 : 4.4 * (ℓ + 5) ^ 2 ≤ L := by linarith
    have h2 : L ≤ L ^ 4 / 5 := by
      have : (5 : ℝ) ≤ L ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hL 3]
      have : L * 5 ≤ L * L ^ 3 := mul_le_mul_of_nonneg_left this hL0.le
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  have h1r : t / 2 ≤ 1 - Real.exp (-t) := by
    have h := Real.add_one_le_exp t
    rw [Real.exp_neg]
    have hp : 0 < Real.exp t := Real.exp_pos t
    have : (Real.exp t)⁻¹ ≤ 1 / (1 + t) := by
      rw [one_div]; exact inv_anti₀ (by linarith) (by linarith : 1 + t ≤ Real.exp t)
    have : 1 / (1 + t) ≤ 1 - t / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hr0 : 0 < 1 - Real.exp (-t) := by linarith
  have he : Real.exp (δ ^ 2 / 2 + |a|) ≤ 1.00001 := by
    have h := exp_small_le (t := δ ^ 2 / 2 + |a|) (by positivity) (by linarith)
    linarith
  have hg : Real.exp (-(δ ^ 2 * Γ ^ 2 / 2)) ≤ 3.8e-6 / L ^ 5 := by
    have e : δ ^ 2 * Γ ^ 2 / 2 = (ℓ + 5) ^ 2 / 2 := by rw [← hδΓ]; ring
    rw [e]
    have h1 : -((ℓ + 5) ^ 2 / 2) ≤ -12.5 - 5 * ℓ := by nlinarith [sq_nonneg ℓ]
    refine (Real.exp_le_exp.2 h1).trans ?_
    rw [Real.exp_sub, show (5 : ℝ) * ℓ = ((5 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hℓdef,
      Real.exp_log hL0]
    exact div_le_div_of_nonneg_right exp_neg_125_le (by positivity)
  -- `Z3g(Γ) ≤ 36ℓ`
  have hZ : Z3g BPz2 Γ ≤ 36 * ℓ := by
    unfold Z3g
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
    have h := log_BPz2_le' Γ
    rw [abs_of_pos hΓ0] at h
    have e4 : 4 * ℓ = Real.log (L ^ 4) := by rw [hℓdef, Real.log_pow]; norm_num
    have h1 : Real.log (Γ + 22) ≤ 4 * ℓ := by
      rw [e4]; apply Real.log_le_log (by positivity); rw [hΓ]; linarith
    have h2 : Real.log (1.25 * (Γ + 11)) ≤ 4 * ℓ := by
      rw [e4]; apply Real.log_le_log (by positivity); rw [hΓ]; linarith
    have := log_10_3_ge
    nlinarith
  have hZ0 : 0 ≤ Z3g BPz2 Γ := by
    unfold Z3g; exact div_nonneg (polyDatum_zeta2.log_pos _).le (lt_of_lt_of_le (by norm_num) log_10_3_ge).le
  have hc : c3g 10 Γ ≤ 36.6 / Γ := by
    unfold c3g
    rw [div_div, div_le_div_iff₀ (by have := log_10_3_ge; positivity) hΓ0]
    have := log_10_3_ge; nlinarith
  have hc0 : 0 ≤ c3g 10 Γ := by
    unfold c3g; exact div_nonneg (by positivity) (lt_of_lt_of_le (by norm_num) log_10_3_ge).le
  have hA : 2 * Z3g BPz2 Γ / (1 - Real.exp (-t)) ≤ 2.12 * Γ := by
    rw [div_le_iff₀ hr0]
    have : 2 * Z3g BPz2 Γ ≤ 72 * ℓ := by linarith
    have hm : 2.12 * Γ * (t / 2) ≤ 2.12 * Γ * (1 - Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left h1r (by positivity)
    have : 72 * ℓ ≤ 2.12 * Γ * (t / 2) := by
      have : 2.12 * Γ * (t / 2) = 1.06 * (t * Γ) := by ring
      rw [this, htΓ]
      have hq : 15.46 * (ℓ + 5) ≤ (ℓ + 5) * (ℓ + 5) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      nlinarith
    linarith
  have hB : 2 * c3g 10 Γ / (1 - Real.exp (-t)) ^ 2 ≤ 3e-4 * Γ := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (t / 2) ^ 2 ≤ (1 - Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (by positivity) h1r 2
    have h3 : 2 * c3g 10 Γ ≤ 73.2 / Γ := by
      calc 2 * c3g 10 Γ ≤ 2 * (36.6 / Γ) := by linarith
        _ = 73.2 / Γ := by ring
    have h4 : 73.2 / Γ ≤ 3e-4 * Γ * (t / 2) ^ 2 := by
      rw [div_le_iff₀ hΓ0]
      have e : 3e-4 * Γ * (t / 2) ^ 2 * Γ = 7.5e-5 * (t * Γ) ^ 2 := by ring
      rw [e, htΓ]
      have : (15.46 : ℝ) ≤ ℓ + 5 := by linarith
      have h5 : (15.46 : ℝ) ^ 4 ≤ (ℓ + 5) ^ 4 := pow_le_pow_left₀ (by norm_num) this 4
      have e2 : 7.5e-5 * (4.4 * (ℓ + 5) ^ 2) ^ 2 = 1.452e-3 * (ℓ + 5) ^ 4 := by ring
      rw [e2]
      have : (73.2 : ℝ) ≤ 1.452e-3 * 15.46 ^ 4 := by norm_num
      linarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 3e-4 * Γ)
    linarith
  have hS0 : 0 ≤ 2 * Z3g BPz2 Γ / (1 - Real.exp (-t)) + 2 * c3g 10 Γ / (1 - Real.exp (-t)) ^ 2 := by positivity
  have hE : 2 * Real.exp (δ ^ 2 / 2 + |a|) * Real.exp (-(δ ^ 2 * Γ ^ 2 / 2)) / Γ ≤ 2 * 1.00001 * (3.8e-6 / L ^ 5) / Γ := by
    gcongr
  calc 2 * Real.exp (δ ^ 2 / 2 + |a|) * Real.exp (-(δ ^ 2 * Γ ^ 2 / 2)) / Γ *
        (2 * Z3g BPz2 Γ / (1 - Real.exp (-t)) + 2 * c3g 10 Γ / (1 - Real.exp (-t)) ^ 2)
      ≤ 2 * 1.00001 * (3.8e-6 / L ^ 5) / Γ * (2.12 * Γ + 3e-4 * Γ) :=
        mul_le_mul hE (add_le_add hA hB) hS0 (by positivity)
    _ = 2 * 1.00001 * 3.8e-6 * 2.1203 / L ^ 5 := by field_simp; ring
    _ ≤ 1e-4 / L ^ 3 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (1 : ℝ) ≤ L ^ 2 := by nlinarith
        nlinarith [pow_pos hL0 3]

end TernaryGoldbach.Explicit
