import TernaryGoldbach.MajorArcs.Cor713

/-!
# [B, Prop 7.1.5] from [B, Prop 9.5.1] and Platt's verification

`Σ Λ(n) (log n) η₊²(n/x) = x ∫ η₊²(t) log(xt) dt + O*(err) x log x` ([B, Prop 9.5.1], cited, conditional on
RH up to `T₀ ≥ 2H + 25`, `H = 200`), with `T₀ = 440` (RH for `ζ` up to `440` follows from `platt_odd`,
`q = 1`), and the value of the integral ([B, (9.94)], numerical axiom).
-/

open Real Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (etaPlus)

/-- The error term (9.73) of [B, Prop 9.5.1] with `H = 200`, `T₁ = T₀ − 400`. -/
noncomputable def err951 (T0 x : ℝ) : ℝ :=
  ((0.462 * Real.log (T0 - 400) ^ 2 / Real.log x + 0.909 * Real.log (T0 - 400)) * (T0 - 400) +
      1.71 * (1 + Real.log (T0 - 400) / Real.log x) * 200) * Real.exp (-(π / 4) * (T0 - 400)) +
    (2.445 * √T0 * Real.log T0 + 50.04) / √x

/-- **[B, Prop 9.5.1]** — *cited* (explicit formula, Lemmas 9.1.1, 9.1.3, 9.1.4), for `η₊` with
`H = 200`: if RH holds up to height `T₀ ≥ max(2H + 25, 200) = 425` and `x ≥ 10⁸`, then
`Σ Λ(n) (log n) η₊²(n/x) = x ∫_0^∞ η₊²(t) log(xt) dt + O*(err_{ℓ₂,η₊}) x log x`. -/
theorem prop_9_5_1 {x : ℝ} (hx : 1e8 ≤ x) {T0 : ℝ} (hT0 : 425 ≤ T0)
    (hG : GRHUpTo (1 : DirichletCharacter ℂ 1) T0) :
    |∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 -
        x * ∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t)| ≤ err951 T0 x * (x * Real.log x) := by
  sorry

/-- **Numerical axiom** ([B, (9.94)]): `∫_0^∞ η₊²(t) log(xt) dt = (0.640206 + O*(1.95·10⁻⁶)) log x −
0.021095 + O*(5.3·10⁻⁷)` for `x ≥ 1`. [B] obtains it from rigorous numerical integration (VNODE-LP) of
`η◦` (`∫ η◦² = 0.64020599736635…`, `∫ η◦² log t = −0.021094778698867…`) and the bounds (A.23), (A.24) on
`η₊ − η◦`. -/
axiom integral_etaPlus_sq_log {x : ℝ} (hx : 1 ≤ x) :
    |(∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t)) - (0.640206 * Real.log x - 0.021095)| ≤
      1.95e-6 * Real.log x + 5.3e-7

theorem log_ge_1e12 {x : ℝ} (hx : 1e12 ≤ x) : 27 ≤ Real.log x := by
  have h : (27 : ℝ) ≤ Real.log 1e12 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 27 = Real.exp 1 ^ 27 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 27 ≤ (2.7182818286 : ℝ) ^ 27 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 27
      _ ≤ 1e12 := by norm_num
  exact h.trans (Real.log_le_log (by norm_num) hx)

theorem err951_le {x : ℝ} (hx : 1e12 ≤ x) : err951 440 x ≤ 1e-10 + 363 / √x := by
  have hlx := log_ge_1e12 hx
  have hl40 : Real.log (440 - 400) ≤ 3.69 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := exp_split_ge 3 (u := 0.69) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith
  have hl40' : 0 ≤ Real.log (440 - 400) := Real.log_nonneg (by norm_num)
  have hl440 : Real.log 440 ≤ 6.09 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := exp_split_ge 6 (u := 0.09) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith
  have hl4400 : 0 ≤ Real.log 440 := Real.log_nonneg (by norm_num)
  have hs440 : √(440 : ℝ) ≤ 21 := by
    rw [show (21 : ℝ) = √(21 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hexp : Real.exp (-(π / 4) * (440 - 400)) ≤ 2.4e-14 := by
    have hπ := Real.pi_gt_d2
    have h1 : Real.exp (-(π / 4) * (440 - 400)) ≤ Real.exp (-31.4) :=
      Real.exp_le_exp.2 (by nlinarith)
    refine h1.trans ?_
    rw [show (-31.4 : ℝ) = -(31 + 0.4) by norm_num, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _)
      (by norm_num)]
    have h := exp_split_ge 31 (u := 0.4) (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    norm_num at h; linarith
  have hsx : 0 < √x := Real.sqrt_pos.2 (by linarith)
  unfold err951
  have hA : (0.462 * Real.log (440 - 400) ^ 2 / Real.log x + 0.909 * Real.log (440 - 400)) * (440 - 400) +
      1.71 * (1 + Real.log (440 - 400) / Real.log x) * 200 ≤ 1000 := by
    have h1 : 0.462 * Real.log (440 - 400) ^ 2 / Real.log x ≤ 0.462 * (3.69 ^ 2 / 27) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div₀ (by norm_num) (pow_le_pow_left₀ hl40' hl40 2) (by norm_num) hlx) (by norm_num)
    have h2 : Real.log (440 - 400) / Real.log x ≤ 3.69 / 27 :=
      div_le_div₀ (by norm_num) hl40 (by norm_num) hlx
    norm_num at h1 h2 ⊢
    linarith
  have hA0 : 0 ≤ (0.462 * Real.log (440 - 400) ^ 2 / Real.log x + 0.909 * Real.log (440 - 400)) *
      (440 - 400) + 1.71 * (1 + Real.log (440 - 400) / Real.log x) * 200 := by positivity
  have hB : (2.445 * √(440 : ℝ) * Real.log 440 + 50.04) / √x ≤ 363 / √x := by
    apply div_le_div_of_nonneg_right _ hsx.le
    have : √(440 : ℝ) * Real.log 440 ≤ 21 * 6.09 :=
      mul_le_mul hs440 hl440 hl4400 (by norm_num)
    nlinarith
  have := mul_le_mul hA hexp (Real.exp_pos _).le (by norm_num)
  linarith

/-- **[B, Prop 7.1.5]**, proved from [B, Prop 9.5.1] (cited), Platt's verification at `q = 1` and the
numerical value (9.94). -/
theorem prop_7_1_5' {x : ℝ} (hx : 1e12 ≤ x) :
    ∃ E₂ : ℝ, |E₂| ≤ 2e-6 + 366.91 / √x ∧
      ∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 =
        0.640206 * x * Real.log x - 0.021095 * x + E₂ * x * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlx := log_ge_1e12 hx
  have hlx0 : 0 < Real.log x := by linarith
  have hxl : 0 < x * Real.log x := mul_pos hx0 hlx0
  have hG : GRHUpTo (1 : DirichletCharacter ℂ 1) 440 :=
    (platt_odd (q := 1) odd_one (by norm_num) 1 DirichletCharacter.isPrimitive_one_level_one).mono
      (by norm_num)
  have h1 := prop_9_5_1 (x := x) (by linarith) (by norm_num) hG
  have h2 := integral_etaPlus_sq_log (by linarith : (1 : ℝ) ≤ x)
  have h3 := err951_le hx
  set S := ∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2
  set I := ∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t)
  refine ⟨(S - (0.640206 * x * Real.log x - 0.021095 * x)) / (x * Real.log x), ?_, ?_⟩
  · rw [abs_div, abs_of_pos hxl, div_le_iff₀ hxl]
    have e : S - (0.640206 * x * Real.log x - 0.021095 * x) =
        (S - x * I) + x * (I - (0.640206 * Real.log x - 0.021095)) := by ring
    rw [e]
    have h4 : |x * (I - (0.640206 * Real.log x - 0.021095))| ≤ x * (1.95e-6 * Real.log x + 5.3e-7) := by
      rw [abs_mul, abs_of_pos hx0]; exact mul_le_mul_of_nonneg_left h2 hx0.le
    have h5 : x * (1.95e-6 * Real.log x + 5.3e-7) ≤ (1.95e-6 + 2e-8) * (x * Real.log x) := by
      have : 5.3e-7 ≤ 2e-8 * Real.log x := by nlinarith
      nlinarith
    have h6 : err951 440 x * (x * Real.log x) ≤ (1e-10 + 363 / √x) * (x * Real.log x) :=
      mul_le_mul_of_nonneg_right h3 hxl.le
    have h7 : (1e-10 + 363 / √x) + (1.95e-6 + 2e-8) ≤ 2e-6 + 366.91 / √x := by
      have : 363 / √x ≤ 366.91 / √x :=
        div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
      linarith
    calc |S - x * I + x * (I - (0.640206 * Real.log x - 0.021095))|
        ≤ |S - x * I| + |x * (I - (0.640206 * Real.log x - 0.021095))| := abs_add_le _ _
      _ ≤ (1e-10 + 363 / √x) * (x * Real.log x) + (1.95e-6 + 2e-8) * (x * Real.log x) := by
          linarith
      _ = ((1e-10 + 363 / √x) + (1.95e-6 + 2e-8)) * (x * Real.log x) := by ring
      _ ≤ (2e-6 + 366.91 / √x) * (x * Real.log x) := mul_le_mul_of_nonneg_right h7 hxl.le
  · field_simp
    ring

end TernaryGoldbach.MajorArcs
