import TernaryGoldbach.MajorArcs.Cor713
import TernaryGoldbach.Explicit.EtaPlusSqBound
import TernaryGoldbach.Explicit.EtaPlusCg
import TernaryGoldbach.MajorArcs.EtaPlusSqLog

/-!
# [B, Prop 9.5.1] (proved, our constants) and [B, Prop 7.1.5]

`Σ Λ(n) (log n) η₊²(n/x) = x ∫ η₊²(t) log(xt) dt + O*(10⁻⁸) x log x` for `x ≥ 4.9·10²⁶`, under RH up to
`500` (from `platt_odd`, `q = 1`): `log n = log x + log(n/x)` splits the sum into the `ζ` explicit formulas
for `η₊²` and `η₊² log` (`Explicit/EtaPlusSqBound.lean`, `T₀ = 500`). With the value of the integral
([B, (9.94)], `EtaPlusSqLog.lean`) this gives [B, Prop 7.1.5].
-/

open Real Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (etaPlus)
open TernaryGoldbach.Explicit (Cg aH Z3g ZLg E1g E2g c3g BPz2 VgL Jl SsumG phi1 phi2 cA_sq_le)

theorem log_ge_1e12 {x : ℝ} (hx : 1e12 ≤ x) : 27 ≤ Real.log x := by
  have h : (27 : ℝ) ≤ Real.log 1e12 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 27 = Real.exp 1 ^ 27 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc Real.exp 1 ^ 27 ≤ (2.7182818286 : ℝ) ^ 27 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 27
      _ ≤ 1e12 := by norm_num
  exact h.trans (Real.log_le_log (by norm_num) hx)

/-! ## [B, Prop 9.5.1] -/

theorem log_le_of_exp_le' {y c : ℝ} (hy : 0 < y) (h : y ≤ Real.exp c) : Real.log y ≤ c :=
  (Real.log_le_iff_le_exp hy).2 h

theorem log525_le : Real.log 525.48 ≤ 6.265 := by
  refine log_le_of_exp_le' (by norm_num) ?_
  have h := exp_split_ge 6 (u := 0.265) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log643_le : Real.log 643.1 ≤ 6.467 := by
  refine log_le_of_exp_le' (by norm_num) ?_
  have h := exp_split_ge 6 (u := 0.467) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_BPz2_500_le : Real.log (BPz2 (500 + 3.48) / 0.355) ≤ 74.71 := by
  have hT : BPz2 (500 + 3.48) ≤ 9201 * 525.48 * 643.1 ^ 9 := by
    unfold BPz2
    rw [abs_of_pos (by norm_num : (0:ℝ) < 500 + 3.48)]
    norm_num
  have hpos : (0:ℝ) < 9201 * 525.48 * 643.1 ^ 9 := by positivity
  have hB0 : 0 < BPz2 (500 + 3.48) := by unfold BPz2; positivity
  refine (Real.log_le_log (div_pos hB0 (by norm_num)) (div_le_div_of_nonneg_right hT (by norm_num))).trans ?_
  rw [Real.log_div hpos.ne' (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have := log9201_le
  have := log525_le
  have := log643_le
  have := neg_log0355_le
  push_cast
  linarith

theorem ZLz500_le : ZLg BPz2 500 ≤ 50.84 := by
  unfold ZLg
  have h := log_BPz2_500_le
  have hl := log_ratio_23_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.polyDatum_zeta2.log_pos (500 + 3.48)]

theorem ZLz500_nonneg : 0 ≤ ZLg BPz2 500 :=
  div_nonneg (Explicit.polyDatum_zeta2.log_pos _).le (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le

theorem Z3z500_le : Z3g BPz2 500 ≤ 62.06 := by
  unfold Z3g
  have hm : Real.log (BPz2 500 / 0.355) ≤ Real.log (BPz2 (500 + 3.48) / 0.355) :=
    Explicit.polyDatum_zeta2.log_mono (by rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]; norm_num)
  have h := hm.trans log_BPz2_500_le
  have hl := log_ratio_3_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.polyDatum_zeta2.log_pos 500]

theorem Z3z500_nonneg : 0 ≤ Z3g BPz2 500 :=
  div_nonneg (Explicit.polyDatum_zeta2.log_pos _).le (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le

theorem Z3z0_le : Z3g BPz2 0 ≤ 33.23 := by
  unfold Z3g
  have h := log_BPz2_zero_le
  have hl := log_ratio_3_ge
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Explicit.polyDatum_zeta2.log_pos 0]

theorem Z3z0_nonneg : 0 ≤ Z3g BPz2 0 :=
  div_nonneg (Explicit.polyDatum_zeta2.log_pos _).le (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le

/-- `E₁` at `T₀ = 500`, from `√(2π Q · 2(T₀ + 3.48)) ≤ S`. -/
theorem E1z500_le {Q1 Q2 S1 S2 : ℝ} (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2)
    (hS1 : 2 * 3.1416 * Q1 * (2 * 503.48) ≤ S1 ^ 2) (hS2 : 2 * 3.1416 * Q2 * (2 * 503.48) ≤ S2 ^ 2)
    (hS1p : 0 ≤ S1) (hS2p : 0 ≤ S2) :
    E1g BPz2 500 (2 * π * Q1) (2 * π * Q2) ≤ 50.84 * (S1 / 3.48 + S2) := by
  set A := (Jl 500 : ℝ) * 3.48 with hA
  have hA1 : A ≤ 500 + 3.48 := by
    rw [hA]; unfold Jl; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 500 / 3.48 by positivity)
    rw [le_div_iff₀ (by norm_num)] at this
    linarith
  have hA0 : 0 ≤ A := by positivity
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have h1 : √(2 * π * Q1 * (2 * A)) ≤ S1 := by
    rw [Real.sqrt_le_left hS1p]
    calc 2 * π * Q1 * (2 * A) ≤ 2 * 3.1416 * Q1 * (2 * 503.48) := by gcongr; linarith
      _ ≤ S1 ^ 2 := hS1
  have h2 : √(2 * π * Q2 * (2 * A)) ≤ S2 := by
    rw [Real.sqrt_le_left hS2p]
    calc 2 * π * Q2 * (2 * A) ≤ 2 * 3.1416 * Q2 * (2 * 503.48) := by gcongr; linarith
      _ ≤ S2 ^ 2 := hS2
  unfold E1g
  rw [← hA]
  have hX : (1 / 3.48) * √(2 * π * Q1 * (2 * A)) + √(2 * π * Q2 * (2 * A)) ≤ S1 / 3.48 + S2 := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 1 / 3.48)
    have e : S1 / 3.48 = 1 / 3.48 * S1 := by ring
    linarith
  have hX0 : 0 ≤ (1 / 3.48) * √(2 * π * Q1 * (2 * A)) + √(2 * π * Q2 * (2 * A)) := by positivity
  exact mul_le_mul ZLz500_le hX hX0 (by norm_num)

theorem rhoP_le : Real.exp (-2.64) ≤ 0.0714 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have h := exp_split_ge 2 (u := 0.64) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem exp_neg60_le : Real.exp (-60) ≤ 1e-26 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := exp_nat_ge 60
  norm_num at this ⊢; linarith

theorem exp_neg597_le : Real.exp (0.3 - 60) ≤ 3e-26 := by
  refine (Real.exp_le_exp.2 (show (0.3 : ℝ) - 60 ≤ -(59:ℕ) by norm_num)).trans ?_
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := exp_nat_ge 59
  norm_num at this ⊢; linarith

/-- `E₂` at `T₀ = 500` for a tail `E_B ρ^k`, `ρ = e^{−2.64}`. -/
theorem E2z500_le {EB : ℝ} (hEB : 0 ≤ EB) :
    E2g BPz2 10 500 EB 0 (Real.exp (-2.64)) 0 ≤ EB * 134.3 := by
  have hρ := rhoP_le
  have hρ0 := (Real.exp_pos (-2.64)).le
  have hi : 1 / (1 - Real.exp (-2.64)) ≤ 1.08 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hi0 : 0 ≤ 1 / (1 - Real.exp (-2.64)) := by rw [one_div]; exact inv_nonneg.2 (by linarith)
  have hc : c3g 10 500 ≤ 0.0731 := by
    unfold c3g
    have hl := log_ratio_3_ge
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hc0 : 0 ≤ c3g 10 500 :=
    div_nonneg (by norm_num) (Explicit.log_ratio_pos (by norm_num) (by norm_num)).le
  have hZ := Z3z500_le
  have hZ0 := Z3z500_nonneg
  unfold E2g
  rw [zero_mul, add_zero, div_eq_mul_one_div (2 * Z3g BPz2 500) (1 - Real.exp (-2.64)),
    div_eq_mul_one_div (2 * c3g 10 500) ((1 - Real.exp (-2.64)) ^ 2), ← one_div_pow]
  have hX : 2 * Z3g BPz2 500 * (1 / (1 - Real.exp (-2.64))) +
      2 * c3g 10 500 * (1 / (1 - Real.exp (-2.64))) ^ 2 ≤ 134.3 := by
    have h1 : Z3g BPz2 500 * (1 / (1 - Real.exp (-2.64))) ≤ 62.06 * 1.08 := mul_le_mul hZ hi hi0 (by norm_num)
    have h2 : c3g 10 500 * (1 / (1 - Real.exp (-2.64))) ^ 2 ≤ 0.0731 * 1.08 ^ 2 :=
      mul_le_mul hc (pow_le_pow_left₀ hi0 hi 2) (by positivity) (by norm_num)
    nlinarith
  exact mul_le_mul_of_nonneg_left hX hEB

theorem log2_const_le' : 2 / Real.log 2 + 4.8 ≤ 7.6855 := by
  have := Real.log_two_gt_d9
  rw [← le_sub_iff_add_le, div_le_iff₀ (by linarith)]; nlinarith

theorem VgL400_le {Kv Kb : ℝ} (hK : Kv ≤ Kb) (hK0 : 0 ≤ Kv) : VgL 3 Kv (1 / 400) ≤ Kb * 6.6403e6 := by
  have hKb : 0 ≤ Kb := hK0.trans hK
  unfold VgL
  have hl := log2_const_le'
  have hl0 : 0 ≤ 2 / Real.log 2 + 4.8 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  have e : ((3:ℝ) + 37) * (2 / (1 / 400)) + 2.6 * (2 / (1 / 400) ^ 2) = 864000 := by norm_num
  rw [e]
  calc Kv * (2 / Real.log 2 + 4.8) * 864000 ≤ Kb * 7.6855 * 864000 := by gcongr
    _ ≤ Kb * 6.6403e6 := by nlinarith [hK0.trans hK]

/-- The relative error, for `x ≥ 4.9·10²⁶`. -/
theorem err_rel {x G E1 E2 V Gb E1b E2b Vb : ℝ} (hx : 4.9e26 ≤ x) (hG : G ≤ Gb) (hGb : 0 ≤ Gb)
    (hE1 : E1 ≤ E1b) (hE1b : 0 ≤ E1b) (hE2 : E2 ≤ E2b) (hV : V ≤ Vb) (hVb : 0 ≤ Vb) :
    G + √x * E1 + x * E2 + x ^ (-(1 / 2) : ℝ) * V / (2 * π) ≤
      (Gb / 4.9e26 + E1b / 2.2135e13 + E2b + Vb / 1e40) * x := by
  have hx0 : 0 < x := by linarith
  have hs : 2.2135e13 ≤ √x := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < √x := by linarith
  have hsx : √x * √x = x := Real.mul_self_sqrt hx0.le
  have t1 : G ≤ Gb / 4.9e26 * x := by
    have : Gb / 4.9e26 * 4.9e26 ≤ Gb / 4.9e26 * x := mul_le_mul_of_nonneg_left hx (by positivity)
    have e : Gb / 4.9e26 * 4.9e26 = Gb := by field_simp
    linarith
  have t2 : √x * E1 ≤ E1b / 2.2135e13 * x := by
    have h1 : √x * E1 ≤ √x * E1b := mul_le_mul_of_nonneg_left hE1 hs0.le
    have h2 : √x * E1b ≤ E1b / 2.2135e13 * x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      have h3 := mul_le_mul_of_nonneg_left hs (mul_nonneg hE1b hs0.le)
      have h4 : E1b * √x * √x = E1b * x := by rw [mul_assoc, hsx]
      linarith
    linarith
  have t3 : x * E2 ≤ E2b * x := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hE2 hx0.le
  have t4 : x ^ (-(1 / 2) : ℝ) * V / (2 * π) ≤ Vb / 1e40 * x := by
    have hrp : x ^ (-(1 / 2) : ℝ) = 1 / √x := by
      rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, one_div]
    rw [hrp]
    have hpi := Real.pi_gt_three
    have hV0 : V ≤ Vb := hV
    have h1 : 1 / √x * V / (2 * π) ≤ 1 / √x * Vb / (2 * π) := by
      have : 1 / √x * V ≤ 1 / √x * Vb := mul_le_mul_of_nonneg_left hV (by positivity)
      exact div_le_div_of_nonneg_right this (by positivity)
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h2 : 1 / √x * Vb ≤ Vb / 2.2135e13 := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_left hVb (by norm_num) hs
    have h3 : Vb / 2.2135e13 ≤ Vb / 1e40 * 4.9e26 * (2 * 3) := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    have h4 : Vb / 1e40 * 4.9e26 * (2 * 3) ≤ Vb / 1e40 * x * (2 * π) := by
      apply mul_le_mul _ (by linarith) (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left hx (by positivity)
    linarith
  nlinarith

theorem err_phi1_le {x : ℝ} (hx : 4.9e26 ≤ x)
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 500 → ρ.re = 1 / 2) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) phi1 x - mellin phi1 1 * x‖ ≤ 2.7e-9 * x := by
  have hx0 : 0 < x := by linarith
  have hc := cA_sq_le
  have hc0 : 0 ≤ (Cg * (2 * aH)) ^ 2 := sq_nonneg _
  have hG : (Cg * (2 * aH)) ^ 2 * 8 * Z3g BPz2 0 ≤ 4.5e6 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_right hc (by norm_num : (0:ℝ) ≤ 8)) Z3z0_le Z3z0_nonneg
      (by norm_num)
    linarith
  have hE1 := E1z500_le (Q1 := 65.5) (Q2 := 147.7) (S1 := 644) (S2 := 967) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hEB : (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (-60) ≤ 16703 * 8 * 1e-26 :=
    mul_le_mul (mul_le_mul_of_nonneg_right hc (by norm_num)) exp_neg60_le (Real.exp_pos _).le
      (by norm_num)
  have hE2 := E2z500_le (EB := (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (-60)) (by positivity)
  have hK : (Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1 ≤ 16703 * 8 * 2.7182818286 :=
    mul_le_mul (mul_le_mul_of_nonneg_right hc (by norm_num)) Real.exp_one_lt_d9.le (Real.exp_pos _).le
      (by norm_num)
  have hV := VgL400_le hK (by positivity)
  refine (Explicit.norm_SsumG_phi1_le (by linarith) hRH).trans ?_
  refine (err_rel hx hG (by norm_num) hE1 (by norm_num) (hE2.trans (mul_le_mul_of_nonneg_right hEB
    (by norm_num))) hV (by norm_num)).trans (mul_le_mul_of_nonneg_right ?_ hx0.le)
  norm_num

theorem err_phi2_le {x : ℝ} (hx : 4.9e26 ≤ x)
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 500 → ρ.re = 1 / 2) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) phi2 x - mellin phi2 1 * x‖ ≤ 4.1e-9 * x := by
  have hx0 : 0 < x := by linarith
  have hc := cA_sq_le
  have hc0 : 0 ≤ (Cg * (2 * aH)) ^ 2 := sq_nonneg _
  have hG : 2 * ((Cg * (2 * aH)) ^ 2 * 8) * Z3g BPz2 0 ≤ 9e6 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_right hc (by norm_num : (0:ℝ) ≤ 8)) Z3z0_le Z3z0_nonneg
      (by norm_num)
    nlinarith
  have hE1 := E1z500_le (Q1 := 147.7) (Q2 := 338.2) (S1 := 967) (S2 := 1463) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hEB : 2 * (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (0.3 - 60) ≤ 2 * 16703 * 8 * 3e-26 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_right hc (by norm_num : (0:ℝ) ≤ 8)) exp_neg597_le
      (Real.exp_pos _).le (by norm_num)
    nlinarith
  have hE2 := E2z500_le (EB := 2 * (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (0.3 - 60)) (by positivity)
  have he800 : Real.exp (1 / 800) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
  have hK : 2 * ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1 * Real.exp (1 / 800)) ≤
      2 * (16703 * 8 * 2.7182818286 * 2.7182818286) := by
    have he := Real.exp_one_lt_d9.le
    have h1 : (Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1 ≤ 16703 * 8 * 2.7182818286 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc (by norm_num)) he (Real.exp_pos _).le (by norm_num)
    have h2 := mul_le_mul h1 (he800.trans he) (Real.exp_pos _).le (by norm_num)
    linarith
  have hV := VgL400_le hK (by positivity)
  refine (Explicit.norm_SsumG_phi2_le (by linarith) hRH).trans ?_
  refine (err_rel hx hG (by norm_num) hE1 (by norm_num) (hE2.trans (mul_le_mul_of_nonneg_right hEB
    (by norm_num))) hV (by norm_num)).trans (mul_le_mul_of_nonneg_right ?_ hx0.le)
  norm_num

theorem mellin_one_eq {φ : ℝ → ℂ} : mellin φ 1 = ∫ t in Ioi (0:ℝ), φ t := by
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp

theorem integrableOn_of_mellinConvergent_one {φ : ℝ → ℂ} (h : MellinConvergent φ 1) :
    IntegrableOn φ (Ioi 0) := by
  unfold MellinConvergent at h
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp

/-- **[B, Prop 9.5.1]** (proved, our constants): if RH holds up to height `500` and `x ≥ 4.9·10²⁶`, then
`Σ Λ(n) (log n) η₊²(n/x) = x ∫_0^∞ η₊²(t) log(xt) dt + O*(10⁻⁸) x log x`. -/
theorem prop_9_5_1 {x : ℝ} (hx : 4.9e26 ≤ x) (hG : GRHUpTo (1 : DirichletCharacter ℂ 1) 500) :
    |∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 -
        x * ∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t)| ≤ 1e-8 * (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx := log_ge_1e12 (by linarith : (1e12:ℝ) ≤ x)
  have hlx0 : 0 < Real.log x := by linarith
  have hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ 500 → ρ.re = 1 / 2 := by
    intro ρ h0 h1 h2 h3
    exact hG ρ (by rw [Explicit.LFunction_one_mod_one]; exact h0) h1 h2 h3
  have h1 := err_phi1_le hx hRH
  have h2 := err_phi2_le hx hRH
  set χ := (1 : DirichletCharacter ℂ 1)
  have hs1 := Explicit.summable_SsumG χ Explicit.goodSmoothing_phi1 hx0
  have hs2 := Explicit.summable_SsumG χ Explicit.goodSmoothing_phi2 hx0
  have hχ : ∀ n : ℕ, χ n = 1 := fun n => by rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  have hA : ((∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 : ℝ) : ℂ) =
      (Real.log x : ℂ) * SsumG χ phi1 x + SsumG χ phi2 x := by
    rw [Complex.ofReal_tsum, SsumG, SsumG, ← tsum_mul_left, ← (hs1.mul_left _).tsum_add hs2]
    congr 1; ext n
    rw [hχ]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hlog : Real.log n = Real.log x + Real.log (n / x) := by
        rw [Real.log_div (by positivity) hx0.ne']; ring
      simp only [phi2, phi1]
      rw [hlog]
      push_cast
      ring
  have m1 : MellinConvergent phi1 1 := mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := -2) one_pos
    (Explicit.continuousOn_phi1.locallyIntegrableOn measurableSet_Ioi) Explicit.phi1_isBigO_top
    Explicit.phi1_isBigO_bot (by norm_num)
  have m2 : MellinConvergent phi2 1 := (Explicit.hasDerivAt_mellin_phi1 (s := 1) (by norm_num)).1
  have i1 := integrableOn_of_mellinConvergent_one m1
  have i2 := integrableOn_of_mellinConvergent_one m2
  have hI : ((∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t) : ℝ) : ℂ) =
      (Real.log x : ℂ) * mellin phi1 1 + mellin phi2 1 := by
    rw [← integral_complex_ofReal, mellin_one_eq, mellin_one_eq, ← integral_const_mul,
      ← integral_add (i1.const_mul _) i2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [phi1, phi2]
    rw [Real.log_mul hx0.ne' ht.ne']
    push_cast
    ring
  have key : ((∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 -
      x * ∫ t in Ioi 0, etaPlus t ^ 2 * Real.log (x * t) : ℝ) : ℂ) =
      (Real.log x : ℂ) * (SsumG χ phi1 x - mellin phi1 1 * x) + (SsumG χ phi2 x - mellin phi2 1 * x) := by
    rw [Complex.ofReal_sub, Complex.ofReal_mul, hA, hI]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlx0]
  have := mul_le_mul_of_nonneg_left h1 hlx0.le
  nlinarith

/-- **[B, Prop 7.1.5]** (for `x ≥ 4.9·10²⁶`), from [B, Prop 9.5.1] (`prop_9_5_1`), Platt's verification at
`q = 1` and the numerical value (9.94). -/
theorem prop_7_1_5' {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∃ E₂ : ℝ, |E₂| ≤ 2e-6 + 366.91 / √x ∧
      ∑' n : ℕ, Λ n * Real.log n * etaPlus (n / x) ^ 2 =
        0.640206 * x * Real.log x - 0.021095 * x + E₂ * x * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlx := log_ge_1e12 (by linarith : (1e12:ℝ) ≤ x)
  have hlx0 : 0 < Real.log x := by linarith
  have hxl : 0 < x * Real.log x := mul_pos hx0 hlx0
  have hG : GRHUpTo (1 : DirichletCharacter ℂ 1) 500 :=
    (platt_odd (q := 1) odd_one (by norm_num) 1 DirichletCharacter.isPrimitive_one_level_one).mono
      (by norm_num)
  have h1 := prop_9_5_1 hx hG
  have h2 := integral_etaPlus_sq_log (by linarith : (1 : ℝ) ≤ x)
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
    have h7 : (1e-8 : ℝ) + (1.95e-6 + 2e-8) ≤ 2e-6 + 366.91 / √x := by
      have : 0 ≤ 366.91 / √x := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
      linarith
    calc |S - x * I + x * (I - (0.640206 * Real.log x - 0.021095))|
        ≤ |S - x * I| + |x * (I - (0.640206 * Real.log x - 0.021095))| := abs_add_le _ _
      _ ≤ 1e-8 * (x * Real.log x) + (1.95e-6 + 2e-8) * (x * Real.log x) := by
          linarith
      _ = (1e-8 + (1.95e-6 + 2e-8)) * (x * Real.log x) := by ring
      _ ≤ (2e-6 + 366.91 / √x) * (x * Real.log x) := mul_le_mul_of_nonneg_right h7 hxl.le
  · field_simp
    ring

end TernaryGoldbach.MajorArcs
