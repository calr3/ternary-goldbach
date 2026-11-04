import TernaryGoldbach.Explicit.PsiRange1

variable [Fact TernaryGoldbach.RHUpTo]

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

theorem sqrt_big {x : ℝ} (hx : Real.exp 35000 ≤ x) : 1e20 * Real.log x ^ 7 ≤ √x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set L := Real.log x with hLdef
  have hL : 35000 ≤ L := by rw [hLdef, Real.le_log_iff_exp_le hx0]; exact hx
  have hsx : √x = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]; congr 1; ring
  rw [hsx]
  have h := Real.pow_div_factorial_le_exp (x := L / 2) (by linarith) 20
  have h2 : 1e20 * L ^ 7 ≤ (L / 2) ^ 20 / (Nat.factorial 20) := by
    rw [le_div_iff₀ (by positivity)]
    have hL13 : (35000 : ℝ) ^ 13 ≤ L ^ 13 := pow_le_pow_left₀ (by norm_num) hL 13
    have e : (L / 2) ^ 20 = L ^ 7 * L ^ 13 / 2 ^ 20 := by ring
    rw [e]
    have hL7 : 0 < L ^ 7 := by positivity
    have : (1e20 : ℝ) * (Nat.factorial 20) * 2 ^ 20 ≤ 35000 ^ 13 := by norm_num [Nat.factorial]
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **`|ψ(x) − x| ≤ 0.2 x/log³x`** for `x ≥ e^{35000}`. -/
theorem psi_asymp {x : ℝ} (hx : Real.exp 35000 ≤ x) : |psiR x - x| ≤ 0.2 * x / Real.log x ^ 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx1 : 1 < x := lt_of_lt_of_le (by have := Real.add_one_le_exp (35000 : ℝ); linarith) hx
  have hℓ := log_log_ge hx
  have hsb := sqrt_big hx
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log x := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Real.log L := ⟨_, rfl⟩
  rw [← hLdef] at hsb hℓ ⊢
  rw [← hℓdef] at hℓ
  have hL : 35000 ≤ L := by rw [hLdef, Real.le_log_iff_exp_le hx0]; exact hx
  have hL0 : 0 < L := by linarith
  have hL3 : 0 < L ^ 3 := by positivity
  have h105 := asymp_ineq1 hL
  rw [← hℓdef] at h105
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = 5 * (ℓ + 5) / L ^ 4 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = ℓ + 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; have : 0 < ℓ + 5 := by linarith
                         positivity
  have hL4 : (1.5e18 : ℝ) ≤ L ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hL 4; norm_num at this ⊢; linarith
  -- `Kδ ≤ 0.0477/L³`
  have hKδ : K * δ ≤ 0.0477 / L ^ 3 := by
    rw [hK, hδ]
    have h1 : (ℓ + 4) * (5 * (ℓ + 5) / L ^ 4) ≤ 5 * (ℓ + 5) ^ 2 / L ^ 4 := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]; nlinarith
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by positivity) hL3]
    have : L ^ 4 = L * L ^ 3 := by ring
    rw [this]
    have : 5 * (ℓ + 5) ^ 2 ≤ 0.0477 * L := by linarith
    nlinarith
  have hKδ0 : 0 ≤ K * δ := by rw [hK]; have : 0 ≤ ℓ + 4 := by linarith
                              positivity
  have hL3' : (4.2e13 : ℝ) ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hL 3; norm_num at this ⊢; linarith
  have hLL4 : 1e11 * L ≤ L ^ 4 := by
    have : L ^ 4 = L * L ^ 3 := by ring
    rw [this]; nlinarith
  have h5L : 5 * (ℓ + 5) ≤ L := by
    have : 5 * (ℓ + 5) ≤ (ℓ + 5) ^ 2 := by nlinarith
    nlinarith
  have hδK : δ ≤ K := by
    have : δ ≤ 1 := by
      rw [hδ, div_le_one (by positivity)]; nlinarith
    rw [hK]; linarith
  have hδsmall : δ ≤ 1e-11 := by
    rw [hδ, div_le_iff₀ (by positivity)]
    nlinarith
  have hKδsmall : K * δ ≤ 1e-12 := by
    refine hKδ.trans ?_
    rw [div_le_iff₀ hL3]
    have := pow_le_pow_left₀ (by norm_num) hL 3
    norm_num at this ⊢; linarith
  have hδ2 : δ ^ 2 / 2 ≤ 0.001 * (K * δ) := by
    have h1 : δ ≤ 0.002 * K := by rw [hK]; linarith
    have := mul_le_mul_of_nonneg_right h1 hδ0.le
    nlinarith
  have hδΓ : δ * (L ^ 4 / 5) = ℓ + 5 := by rw [hδ]; field_simp
  -- `e^{−K²/2} ≤ 3.4·10⁻⁴/L⁴`
  have hKt : Real.exp (-(K ^ 2 / 2)) ≤ 3.4e-4 / L ^ 4 := by
    have h1 : -(K ^ 2 / 2) ≤ -8 - 4 * ℓ := by rw [hK]; nlinarith [sq_nonneg ℓ]
    refine (Real.exp_le_exp.2 h1).trans ?_
    rw [Real.exp_sub, show (4 : ℝ) * ℓ = ((4 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hℓdef,
      Real.exp_log hL0]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h := exp_split_ge' 8 (u := 0) le_rfl 1
    norm_num at h ⊢; linarith
  have hKt0 : 0 < Real.exp (-(K ^ 2 / 2)) := Real.exp_pos _
  have hKt' : Real.exp (-(K ^ 2 / 2)) ≤ 1e-8 / L ^ 3 := by
    refine hKt.trans ?_
    rw [div_le_div_iff₀ (by positivity) hL3]
    have : L ^ 4 = L * L ^ 3 := by ring
    rw [this]; nlinarith
  have hΓ : (3e12 : ℝ) ≤ L ^ 4 / 5 := by linarith
  have hsx := Real.sqrt_nonneg x
  -- the absolute terms
  have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hL7 : 0 < L ^ 7 := by positivity
  have habs : 15000 * √x + 2.54e-3 * L ^ 4 + 1e11 ≤ 1e-6 * x / L ^ 3 := by
    have h1 : 1e20 * L ^ 7 * √x ≤ x := by
      have := mul_le_mul_of_nonneg_right hsb hsx; rwa [hss] at this
    have h2 : 1 ≤ L ^ 4 := by nlinarith
    have h3 : 1 ≤ √x := by nlinarith
    rw [le_div_iff₀ hL3]
    have e1 : L ^ 7 = L ^ 4 * L ^ 3 := by ring
    have h4 : (15000 * √x + 2.54e-3 * L ^ 4 + 1e11) * L ^ 3 ≤ 1e14 * (L ^ 7 * √x) := by
      have : L ^ 4 * L ^ 3 ≤ L ^ 7 * √x := by rw [← e1]; nlinarith
      have : L ^ 3 ≤ L ^ 7 * √x := by nlinarith
      have : √x * L ^ 3 ≤ L ^ 7 * √x := by nlinarith
      nlinarith
    nlinarith
  have hx19 : (1e19 : ℝ) ≤ x := by
    have h := exp_nat_ge' 44
    have h2 : Real.exp ((44 : ℕ) : ℝ) ≤ Real.exp 35000 := Real.exp_le_exp.2 (by norm_num)
    have : (1e19 : ℝ) ≤ (2.7182818283 : ℝ) ^ 44 := by norm_num
    exact this.trans (h.trans (h2.trans hx))
  -- the explicit-formula errors
  have hErr : ∀ a : ℝ, |a| ≤ K * δ → Real.log (1e10 / x) ≤ a →
      |∑' n : ℕ, Λ n * gsm a (Real.log (1e10 / x)) δ (n / x) -
        Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp (Real.log (1e10 / x))) * x| ≤
        14990 * √x + 0.0101 * x / L ^ 3 + 2.54e-3 * L ^ 4 := by
    intro a ha hab
    have hb0 : Real.log (1e10 / x) ≤ 0 := Real.log_nonpos (by positivity)
      ((div_le_one hx0).2 (by linarith))
    have hT := tsum_gsm_le_zf (a := a) (Γ := L ^ 4 / 5) hδ0 hab hb0 hx1 hΓ
    have hδa : δ ^ 2 / 2 + |a| ≤ 1e-6 := by linarith
    have h1 := LineB_le_gen (a := a) (δ := δ) (by linarith)
    have h2 : MidB a δ (L ^ 4 / 5) x ≤ 0.01 / L ^ 3 := by
      have := MidB_asymp_le (a := a) (δ := δ) hx hδa; rwa [← hLdef] at this
    have h3 : TailBG a δ (L ^ 4 / 5) ≤ 1e-4 / L ^ 3 := by
      have := TailBG_asymp_le (a := a) hx (by rw [← hLdef, ← hℓdef, ← hδ]; exact hδa)
      rwa [← hLdef, ← hℓdef, ← hδ] at this
    have h4 := Vg_le_gen (a := a) (δ := δ) (x := x) hδ0 hδsmall (by linarith) hx19
    have h4' : 2.54e-3 / δ ≤ 2.54e-3 * L ^ 4 := by
      rw [div_le_iff₀ hδ0, hδ]
      have : 1 ≤ 5 * (ℓ + 5) := by linarith
      rw [mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]; nlinarith
    refine hT.trans ?_
    have e1 := mul_le_mul_of_nonneg_left h1 hsx
    have e2 := mul_le_mul_of_nonneg_left h2 hx0.le
    have e3 := mul_le_mul_of_nonneg_left h3 hx0.le
    have e4 := h4.trans h4'
    have hsum := add_le_add (add_le_add (add_le_add e1 e2) e3) e4
    refine hsum.trans ?_
    have : x * (0.01 / L ^ 3) + x * (1e-4 / L ^ 3) ≤ 0.0101 * x / L ^ 3 := by
      rw [show x * (0.01 / L ^ 3) + x * (1e-4 / L ^ 3) = 0.0101 * x / L ^ 3 by ring]
    linarith
  -- the combination
  set q := x / L ^ 3 with hq
  have hq0 : 0 < q := by positivity
  have hqx : q ≤ x := div_le_self hx0.le (by nlinarith)
  have hxq : ∀ c : ℝ, c * x / L ^ 3 = c * q := fun c => by rw [hq]; ring
  have hb0 : Real.log (1e10 / x) ≤ -(K * δ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1e10 / x by positivity)
    have : 1e10 / x ≤ 1e-9 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  rw [hxq] at habs
  have hKt'' : Real.exp (-(K ^ 2 / 2)) ≤ 1e-8 := by
    refine hKt'.trans ?_; rw [div_le_iff₀ hL3]; nlinarith
  -- upper
  have hK1 : 2 * Real.exp (-(K ^ 2 / 2)) < 1 := by linarith
  have hexp1 : Real.exp (K * δ) ≤ 2 := by
    have := exp_small_le (t := K * δ) hKδ0 (by linarith); linarith
  have hYx : 1e10 * Real.exp (K * δ) ≤ x := by nlinarith
  have hEu := hErr (K * δ) (by rw [abs_of_nonneg hKδ0]) (by linarith)
  have hU := psi_upper_of_err (δ := δ) (K := K) (y0 := 1e10) (x := x) hδ0 (by rw [hK]; linarith) hK1
    (by norm_num) hx1.le hYx hEu
  rw [hxq] at hEu hU
  have hexp2 : Real.exp (δ ^ 2 / 2 + K * δ) ≤ 1 + 0.0956 / L ^ 3 := by
    have h := exp_small_le (t := δ ^ 2 / 2 + K * δ) (by positivity) (by linarith)
    have : 2 * (δ ^ 2 / 2 + K * δ) ≤ 2.002 * (0.0477 / L ^ 3) := by nlinarith
    have : 2.002 * (0.0477 / L ^ 3) ≤ 0.0956 / L ^ 3 := by
      rw [show 2.002 * (0.0477 / L ^ 3) = 0.0954954 / L ^ 3 by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hL3.le
    linarith
  set ε := Real.exp (-(K ^ 2 / 2)) with hε
  have hε0 : 0 ≤ ε := hKt0.le
  have hden : 1 / (1 - 2 * ε) ≤ 1 + 4 * ε := by
    rw [div_le_iff₀ (by linarith only [hKt''])]; nlinarith only [hε0, hKt'']
  set N := Real.exp (δ ^ 2 / 2 + K * δ) * x + (14990 * √x + 0.0101 * q + 2.54e-3 * L ^ 4) with hNdef
  have hN : N ≤ x + 0.1058 * q - 1e11 := by
    have h1 := mul_le_mul_of_nonneg_right hexp2 hx0.le
    have e : (1 + 0.0956 / L ^ 3) * x = x + 0.0956 * q := by rw [hq]; ring
    have h2 : 14990 * √x ≤ 15000 * √x := by linarith only [hsx]
    rw [hNdef]
    linarith only [h1, e, h2, habs, hq0, hsx, pow_nonneg hL0.le 4]
  have hN2 : N ≤ 2 * x := by linarith only [hN, hqx, hq0]
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hεx : ε * x ≤ 1e-8 * q := by
    have := mul_le_mul_of_nonneg_right hKt' hx0.le
    rw [show 1e-8 / L ^ 3 * x = 1e-8 * q by rw [hq]; ring] at this; exact this
  have hup : psiR x ≤ x + 0.2 * q := by
    have h1 : N / (1 - 2 * ε) ≤ N + 4 * (ε * N) := by
      rw [div_eq_mul_one_div]
      calc N * (1 / (1 - 2 * ε)) ≤ N * (1 + 4 * ε) := mul_le_mul_of_nonneg_left hden hN0
        _ = N + 4 * (ε * N) := by ring
    have h2 : ε * N ≤ ε * (2 * x) := mul_le_mul_of_nonneg_left hN2 hε0
    have h3 : 4 * (1e10 * Real.exp (K * δ)) ≤ 8e10 := by linarith only [hexp1]
    have h4 : (8e10 : ℝ) ≤ 1e-6 * q := by linarith only [habs, hsx, pow_nonneg hL0.le 4]
    have h5 : ε * (2 * x) = 2 * (ε * x) := by ring
    have : psiR x ≤ 4 * (1e10 * Real.exp (K * δ)) + N / (1 - 2 * ε) := hU
    linarith only [this, h1, h2, h3, h4, h5, hεx, hN]
  -- lower
  have hEl := hErr (-(K * δ)) (by rw [abs_neg, abs_of_nonneg hKδ0]) hb0
  have hL' := psi_lower_of_err (δ := δ) (K := K) (y0 := 1e10) (x := x) hδ0 (by linarith) hδK
    (by norm_num) hx1.le hb0 hEl
  rw [hxq] at hEl hL'
  have hexp3 : 1 - 0.0477 / L ^ 3 ≤ Real.exp (-(K * δ)) := by
    have := Real.add_one_le_exp (-(K * δ)); linarith
  have hlo : x - 0.2 * q ≤ psiR x := by
    have h1 := mul_le_mul_of_nonneg_right hexp3 hx0.le
    have e : (1 - 0.0477 / L ^ 3) * x = x - 0.0477 * q := by rw [hq]; ring
    have h2 : 4 * x * ε ≤ 4e-8 * q := by linarith only [hεx]
    have h4 : 14990 * √x ≤ 15000 * √x := by linarith only [hsx]
    linarith only [hL', h1, e, h2, h4, habs, hq0, hsx, pow_nonneg hL0.le 4]
  rw [abs_le]; constructor
  · rw [hxq]; linarith
  · rw [hxq]; linarith

end TernaryGoldbach.Explicit
