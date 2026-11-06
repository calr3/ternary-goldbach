import TernaryGoldbach.Explicit.PsiLarge

/-!
# `|ψ(x) − x| ≤ 2.1·10⁻¹⁴ x` for `x ≥ e^{20000}`

`δ = 1.4·10⁻¹⁵`, `K₀ = 9`, `Γ = 6.43·10¹⁵`, `y₀ = 10¹⁰`.
-/

open Complex Set Filter MeasureTheory
open scoped Real ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

theorem log_Gam1_le : Real.log (6.43e15 + 22) ≤ 36.41 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 36 (u := 0.41) (by norm_num) 10
  have e : ((36 : ℕ) : ℝ) + 0.41 = 36.41 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_Gam1_le' : Real.log 6.43e15 ≤ 36.41 :=
  (Real.log_le_log (by norm_num) (by norm_num)).trans log_Gam1_le

theorem log_Gam1b_le : Real.log (1.25 * (6.43e15 + 11)) ≤ 36.63 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 36 (u := 0.63) (by norm_num) 10
  have e : ((36 : ℕ) : ℝ) + 0.63 = 36.63 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_neg_499_le : Real.exp (-49.9) ≤ 2.14e-22 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have h := exp_split_ge' 49 (u := 0.9) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem exp_neg_405_le : Real.exp (-40.5) ≤ 2.6e-18 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have h := exp_split_ge' 40 (u := 0.5) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem Z3g_Gam1_le : Z3g BPz2 6.43e15 ≤ 313 := by
  unfold Z3g
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
  have h := log_BPz2_le' 6.43e15
  rw [abs_of_pos (by norm_num)] at h
  have := log_Gam1_le; have := log_Gam1b_le; have := log_10_3_ge
  nlinarith

/-! ## Constants at `3·10¹²` (the upper mid range of `MidB`) -/

theorem log_3e12_hi : Real.log (3e12 + 22) ≤ 28.7298 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 28 (u := 0.7298) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_375e12_hi : Real.log (1.25 * (3e12 + 11)) ≤ 28.9529 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 28 (u := 0.9529) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem Z3g_3e12_le : Z3g BPz2 3e12 ≤ 248.9 := by
  unfold Z3g
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
  have h := log_BPz2_le' 3e12
  rw [abs_of_pos (by norm_num)] at h
  have := log_3e12_hi; have := log_375e12_hi; have := log_10_3_ge
  nlinarith

theorem Z3g_3e12_nonneg : 0 ≤ Z3g BPz2 3e12 := by
  unfold Z3g
  exact div_nonneg (polyDatum_zeta2.log_pos _).le (lt_of_lt_of_le (by norm_num) log_10_3_ge).le

theorem c3g_3e12_le : c3g 10 3e12 ≤ 1.22e-11 := by
  unfold c3g
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
  have := log_10_3_ge
  nlinarith

theorem c3g_3e12_nonneg : 0 ≤ c3g 10 3e12 := by
  unfold c3g; exact div_nonneg (by norm_num) (lt_of_lt_of_le (by norm_num) log_10_3_ge).le

theorem exp_neg_63_le : Real.exp (-63) ≤ 4.4e-28 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := exp_nat_ge' 63
  norm_num at this ⊢; linarith

/-- The lower mid range `(3·10¹⁰, 3·10¹²]` for `log x ≥ 20000`. -/
theorem MidB0_lo_le {a δ x : ℝ} (hδa : δ ^ 2 / 2 + |a| ≤ 1e-10) (hx : 20000 ≤ Real.log x) :
    MidB0 a δ 3e10 3e12 x ≤ 1e-22 := by
  unfold MidB0
  have he : Real.exp (δ ^ 2 / 2 + |a|) ≤ 1.000001 := by
    have h := exp_small_le (t := δ ^ 2 / 2 + |a|) (by positivity) (by linarith)
    linarith
  have hlg := log_3e12_hi
  have hlg' : Real.log 3e12 ≤ 28.7298 := (Real.log_le_log (by norm_num) (by norm_num)).trans hlg
  have hlg0 : 0 < Real.log 3e12 := Real.log_pos (by norm_num)
  have hzf : Real.exp (-(Real.log x / (11 * Real.log 3e12))) ≤ 4.4e-28 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_63_le
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    nlinarith
  have hK : ((⌊((3e12 : ℝ) - 3e10) / 4.4⌋₊ : ℕ) : ℝ) + 1 ≤ 6.76e11 := by
    have := Nat.floor_le (show (0:ℝ) ≤ ((3e12 : ℝ) - 3e10) / 4.4 by norm_num)
    norm_num at this ⊢; try linarith
  have hZ := Z3g_H_le; have hZ0 := Z3g_H_nonneg
  have hc := c3g_H_le; have hc0 := c3g_H_nonneg
  have hK0 : (0:ℝ) ≤ ((⌊((3e12 : ℝ) - 3e10) / 4.4⌋₊ : ℕ) : ℝ) + 1 := by positivity
  calc 2 * Real.exp (δ ^ 2 / 2 + |a|) / 3e10 * Real.exp (-(Real.log x / (11 * Real.log 3e12))) *
        ((((⌊((3e12 : ℝ) - 3e10) / 4.4⌋₊ : ℕ) : ℝ) + 1) * (2 * Z3g BPz2 3e10 + 2 * c3g 10 3e10 *
          (((⌊((3e12 : ℝ) - 3e10) / 4.4⌋₊ : ℕ) : ℝ) + 1)))
      ≤ 2 * 1.000001 / 3e10 * 4.4e-28 * (6.76e11 * (2 * 210.6 + 2 * 1.22e-9 * 6.76e11)) := by
        gcongr
    _ ≤ 1e-22 := by norm_num

theorem MidB_r1_le {a x : ℝ} (ha : |a| ≤ 1.3e-14) (hx : 20000 ≤ Real.log x) :
    MidB a 1.4e-15 6.43e15 x ≤ 7.6e-15 := by
  unfold MidB
  have hlo := MidB0_lo_le (a := a) (δ := 1.4e-15) (by norm_num at ha ⊢; linarith) hx
  suffices h : MidB0 a 1.4e-15 3e12 6.43e15 x ≤ 7.55e-15 by linarith
  unfold MidB0
  have he : Real.exp ((1.4e-15 : ℝ) ^ 2 / 2 + |a|) ≤ 1.000001 := by
    have h := exp_small_le (t := (1.4e-15 : ℝ) ^ 2 / 2 + |a|) (by positivity) (by norm_num at ha ⊢; linarith)
    norm_num at ha h ⊢; linarith
  have hlg := log_Gam1_le'
  have hlg0 : 0 < Real.log 6.43e15 := Real.log_pos (by norm_num)
  have hzf : Real.exp (-(Real.log x / (11 * Real.log 6.43e15))) ≤ 2.14e-22 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_neg_499_le
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    nlinarith
  have hK : ((⌊((6.43e15 : ℝ) - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1 ≤ 1.4614e15 := by
    have := Nat.floor_le (show (0:ℝ) ≤ ((6.43e15 : ℝ) - 3e12) / 4.4 by norm_num)
    norm_num at this ⊢; try linarith
  have hZ := Z3g_3e12_le; have hZ0 := Z3g_3e12_nonneg
  have hc := c3g_3e12_le; have hc0 := c3g_3e12_nonneg
  have hK0 : (0:ℝ) ≤ ((⌊((6.43e15 : ℝ) - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1 := by positivity
  calc 2 * Real.exp ((1.4e-15 : ℝ) ^ 2 / 2 + |a|) / 3e12 * Real.exp (-(Real.log x / (11 * Real.log 6.43e15))) *
        ((((⌊((6.43e15 : ℝ) - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1) * (2 * Z3g BPz2 3e12 + 2 * c3g 10 3e12 *
          (((⌊((6.43e15 : ℝ) - 3e12) / 4.4⌋₊ : ℕ) : ℝ) + 1)))
      ≤ 2 * 1.000001 / 3e12 * 2.14e-22 * (1.4614e15 * (2 * 248.9 + 2 * 1.22e-11 * 1.4614e15)) := by
        gcongr
    _ ≤ 7.55e-15 := by norm_num

theorem TailBG_r1_le {a : ℝ} (ha : |a| ≤ 1.3e-14) : TailBG a 1.4e-15 6.43e15 ≤ 1e-17 := by
  unfold TailBG EBg rhoG
  set t : ℝ := 4.4 * (1.4e-15) ^ 2 * 6.43e15 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have h1r : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have h := Real.add_one_le_exp t
    rw [Real.exp_neg]
    have hp : 0 < Real.exp t := Real.exp_pos t
    rw [div_le_iff₀ (by linarith), sub_mul, one_mul, inv_mul_eq_div]
    have : (1 + t) / Real.exp t ≤ 1 := by rw [div_le_one hp]; linarith
    linarith
  have htv : (5.54e-14 : ℝ) ≤ t / (1 + t) := by rw [le_div_iff₀ (by linarith), ht]; norm_num
  have hr : (5.54e-14 : ℝ) ≤ 1 - Real.exp (-t) := htv.trans h1r
  have he : Real.exp ((1.4e-15 : ℝ) ^ 2 / 2 + |a|) ≤ 1.000001 := by
    have h := exp_small_le (t := (1.4e-15 : ℝ) ^ 2 / 2 + |a|) (by positivity) (by norm_num at ha ⊢; linarith)
    norm_num at ha h ⊢; linarith
  have hg : Real.exp (-((1.4e-15 : ℝ) ^ 2 * (6.43e15 : ℝ) ^ 2 / 2)) ≤ 2.6e-18 :=
    le_trans (Real.exp_le_exp.2 (by norm_num)) exp_neg_405_le
  have hZ := Z3g_Gam1_le
  have hZ0 : 0 ≤ Z3g BPz2 6.43e15 := by
    unfold Z3g; exact div_nonneg (polyDatum_zeta2.log_pos _).le (lt_of_lt_of_le (by norm_num) log_10_3_ge).le
  have hc : c3g 10 6.43e15 ≤ 5.7e-15 := by
    unfold c3g; rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
    have := log_10_3_ge; nlinarith
  have hc0 : 0 ≤ c3g 10 6.43e15 := by
    unfold c3g; exact div_nonneg (by norm_num) (lt_of_lt_of_le (by norm_num) log_10_3_ge).le
  have hr0 : 0 < 1 - Real.exp (-t) := lt_of_lt_of_le (by norm_num) hr
  have hA : 2 * Z3g BPz2 6.43e15 / (1 - Real.exp (-t)) ≤ 2 * 313 / 5.54e-14 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hB : 2 * c3g 10 6.43e15 / (1 - Real.exp (-t)) ^ 2 ≤ 2 * 5.7e-15 / (5.54e-14) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (5.54e-14 : ℝ) ^ 2 ≤ (1 - Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (by norm_num) hr 2
    nlinarith
  have hE : 2 * Real.exp ((1.4e-15 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((1.4e-15 : ℝ) ^ 2 * (6.43e15 : ℝ) ^ 2 / 2)) / 6.43e15 ≤
      2 * 1.000001 * 2.6e-18 / 6.43e15 := by gcongr
  have hS0 : 0 ≤ 2 * Z3g BPz2 6.43e15 / (1 - Real.exp (-t)) + 2 * c3g 10 6.43e15 / (1 - Real.exp (-t)) ^ 2 := by
    positivity
  calc 2 * Real.exp ((1.4e-15 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((1.4e-15 : ℝ) ^ 2 * (6.43e15 : ℝ) ^ 2 / 2)) / 6.43e15 *
        (2 * Z3g BPz2 6.43e15 / (1 - Real.exp (-t)) + 2 * c3g 10 6.43e15 / (1 - Real.exp (-t)) ^ 2)
      ≤ (2 * 1.000001 * 2.6e-18 / 6.43e15) * (2 * 313 / 5.54e-14 + 2 * 5.7e-15 / (5.54e-14) ^ 2) :=
        mul_le_mul hE (add_le_add hA hB) hS0 (by norm_num)
    _ ≤ 1e-17 := by norm_num

theorem LineB_le_gen {a δ : ℝ} (h : δ ^ 2 / 2 + |a| ≤ 3e-11) : LineB a δ ≤ 14990 := by
  unfold LineB
  have he : Real.exp (δ ^ 2 / 2 + |a|) ≤ 1.000001 := by
    have h' := exp_small_le (t := δ ^ 2 / 2 + |a|) (by positivity) (by linarith)
    linarith
  have h1 := ZLg_H_le
  have h2 := log_Jl_H_le
  have hZ0 : 0 ≤ ZLg BPz2 3e10 :=
    div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le
  have hJ0 : 0 ≤ Real.log (Jl 3e10) := Real.log_nonneg (by unfold Jl; norm_num)
  calc ZLg BPz2 3e10 * (2 * Real.exp (δ ^ 2 / 2 + |a|)) * (4 * (1 + (1 + Real.log (Jl 3e10)) / 3.48))
      ≤ 172.6 * (2 * 1.000001) * (4 * (1 + (1 + 22.88) / 3.48)) := by gcongr
    _ ≤ 14990 := by norm_num

theorem Vg_le_gen {a δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1e-11) (ha : |a| ≤ 1e-10) (hx : 1e19 ≤ x) :
    x ^ (-(1 / 2) : ℝ) * Vg a (Real.log (1e10 / x)) δ / (2 * π) ≤ 2.54e-3 / δ := by
  have hx0 : 0 < x := by linarith
  have hsx : x ^ (-(1 / 2) : ℝ) = 1 / √x := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, one_div]
  have hb : Real.exp (-(Real.log (1e10 / x) / 2)) = √x / 1e5 := by
    have h1 : Real.exp (-(Real.log (1e10 / x) / 2)) = √(x / 1e10) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
      congr 1
      rw [show x / 1e10 = (1e10 / x)⁻¹ by field_simp, Real.log_inv]; ring
    rw [h1, Real.sqrt_div' _ (by norm_num), show (1e10 : ℝ) = (1e5) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hS : 3.16e9 ≤ √x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]; norm_num; linarith
  have hS0 : 0 < √x := by linarith
  have hc1 : 2 / Real.log 2 + 4.8 ≤ 7.6856 := by
    have := Real.log_two_gt_d9
    have : 2 / Real.log 2 ≤ 2 / 0.6931 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have : (2 : ℝ) / 0.6931 ≤ 2.8856 := by norm_num
    linarith
  have hc10 : 0 ≤ 2 / Real.log 2 + 4.8 := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  have hδe : Real.exp (δ ^ 2 / 8) ≤ 1.000001 := by
    have h := exp_small_le (t := δ ^ 2 / 8) (by positivity) (by nlinarith)
    have : δ ^ 2 / 8 ≤ 1e-22 := by nlinarith
    linarith
  have hae : Real.exp (-(a / 2)) ≤ 1.000001 := by
    have h1 : -(a / 2) ≤ |a| := by cases abs_cases a <;> linarith
    have h := exp_small_le (t := |a|) (abs_nonneg a) (by linarith)
    have := Real.exp_le_exp.2 h1
    linarith
  have hpi : 2.5066 ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have := Real.pi_gt_d6; nlinarith
  unfold Vg
  rw [hsx, hb]
  set c₁ := 2 / Real.log 2 + 4.8
  set E := Real.exp (δ ^ 2 / 8)
  set A := Real.exp (-(a / 2))
  set P := √(2 * π) with hP
  have hP2 : P * P = 2 * π := Real.mul_self_sqrt (by positivity)
  have e : 1 / √x * (c₁ * 82.6 * E * (A + √x / 1e5) * (P / δ)) / (2 * π) =
      (c₁ * 82.6 * E) * (1 / P) * (A / √x + 1e-5) / δ := by
    rw [← hP2]
    field_simp
    ring
  rw [e]
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have h1 : c₁ * 82.6 * E ≤ 7.6856 * 82.6 * 1.000001 := by gcongr
  have h2 : 1 / P ≤ 1 / 2.5066 := one_div_le_one_div_of_le (by norm_num) hpi
  have h3 : A / √x + 1e-5 ≤ 1.000001 / 3.16e9 + 1e-5 := by
    have : A / √x ≤ 1.000001 / 3.16e9 := div_le_div₀ (by norm_num) hae (by norm_num) hS
    linarith
  apply div_le_div_of_nonneg_right _ hδ.le
  calc (c₁ * 82.6 * E) * (1 / P) * (A / √x + 1e-5)
      ≤ (7.6856 * 82.6 * 1.000001) * (1 / 2.5066) * (1.000001 / 3.16e9 + 1e-5) := by gcongr
    _ ≤ 2.54e-3 := by norm_num

theorem exp_20000_ge : (1e40 : ℝ) ≤ Real.exp 20000 := by
  have h := exp_nat_ge' 93
  have : (1e40 : ℝ) ≤ (2.7182818283 : ℝ) ^ 93 := by norm_num
  have h2 : Real.exp ((93 : ℕ) : ℝ) ≤ Real.exp 20000 := Real.exp_le_exp.2 (by norm_num)
  exact this.trans (h.trans h2)

/-- Large `x`: the absolute terms are negligible. -/
theorem abs_terms_le {x : ℝ} (hx : 1e40 ≤ x) : 15000 * √x + 1e13 ≤ 1.6e-16 * x := by
  have hx0 : 0 < x := by linarith
  have hs : 1e20 ≤ √x := by rw [Real.le_sqrt (by norm_num) hx0.le]; norm_num; linarith
  have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
  have h1 : 15000 * √x ≤ 1.5e-16 * x := by
    have : 15000 * √x ≤ 1.5e-16 * (√x * √x) := by nlinarith
    rwa [hss] at this
  have h2 : (1e13 : ℝ) ≤ 1e-17 * x := by nlinarith
  linarith

variable [Fact TernaryGoldbach.RHUpTo] in
/-- **`|ψ(x) − x| ≤ 2.1·10⁻¹⁴ x`** for `x ≥ e^{20000}`. -/
theorem psi_range1 {x : ℝ} (hx : Real.exp 20000 ≤ x) : |psiR x - x| ≤ 2.1e-14 * x := by
  have hx40 : 1e40 ≤ x := exp_20000_ge.trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlx : 20000 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  set δ : ℝ := 1.4e-15 with hδ
  have hδ0 : 0 < δ := by norm_num
  have hKd : (9 : ℝ) * δ = 1.26e-14 := by rw [hδ]; norm_num
  have hK2 : -((9 : ℝ) ^ 2 / 2) = -40.5 := by norm_num
  have he405 := exp_neg_405_le
  have he405' : 0 < Real.exp (-40.5) := Real.exp_pos _
  have hsx := Real.sqrt_nonneg x
  have habs := abs_terms_le hx40
  have hb0 : Real.log (1e10 / x) ≤ -(1.26e-14) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1e10 / x by positivity)
    have : 1e10 / x ≤ 1e-9 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  -- the error terms
  have hErr : ∀ a : ℝ, |a| ≤ 1.26e-14 → Real.log (1e10 / x) ≤ a →
      |∑' n : ℕ, Λ n * gsm a (Real.log (1e10 / x)) δ (n / x) -
        Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp (Real.log (1e10 / x))) * x| ≤
        14990 * √x + 7.6e-15 * x + 1e-17 * x + 1.82e12 := by
    intro a ha hab
    have hT := tsum_gsm_le_zf (a := a) (Γ := 6.43e15) hδ0 hab (hb0.trans (by norm_num)) hx1 (by norm_num)
    have h1 := LineB_le_gen (a := a) (δ := δ) (by rw [hδ]; norm_num at ha ⊢; linarith)
    have h2 : MidB a δ 6.43e15 x ≤ 7.6e-15 := by rw [hδ]; exact MidB_r1_le (a := a) (x := x) (by linarith) hlx
    have h3 : TailBG a δ 6.43e15 ≤ 1e-17 := by rw [hδ]; exact TailBG_r1_le (a := a) (by linarith)
    have h4 := Vg_le_gen (a := a) (δ := δ) (x := x) hδ0 (by norm_num) (by linarith) (by linarith)
    have h4' : 2.54e-3 / δ ≤ 1.82e12 := by rw [hδ]; norm_num
    refine hT.trans ?_
    have e1 := mul_le_mul_of_nonneg_left h1 hsx
    have e2 := mul_le_mul_of_nonneg_left h2 hx0.le
    have e3 := mul_le_mul_of_nonneg_left h3 hx0.le
    have e4 := h4.trans h4'
    have hsum := add_le_add (add_le_add (add_le_add e1 e2) e3) e4
    refine hsum.trans (le_of_eq ?_)
    ring
  -- upper
  have hK1 : 2 * Real.exp (-((9 : ℝ) ^ 2 / 2)) < 1 := by rw [hK2]; linarith
  have hYx : 1e10 * Real.exp (9 * δ) ≤ x := by
    rw [hKd]
    have h := exp_small_le (t := (1.26e-14 : ℝ)) (by norm_num) (by norm_num)
    have := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 1e10)
    linarith
  have hEu := hErr (9 * δ) (by rw [hKd, abs_of_pos (by norm_num)]) (by rw [hKd]; linarith)
  have hU := psi_upper_of_err (δ := δ) (K := 9) (y0 := 1e10) (x := x) hδ0 (by norm_num) hK1
    (by norm_num) hx1.le hYx hEu
  rw [hK2, hKd] at hU
  have hexp1 : Real.exp (δ ^ 2 / 2 + 1.26e-14) ≤ 1 + 1.2602e-14 := by
    have h := exp_small_le2 (t := δ ^ 2 / 2 + 1.26e-14) (by positivity) (by rw [hδ]; norm_num)
    rw [hδ] at h ⊢; norm_num at h ⊢; linarith
  have hexp2 : Real.exp (1.26e-14) ≤ 1.0000001 := by
    have := exp_small_le (t := (1.26e-14 : ℝ)) (by norm_num) (by norm_num); norm_num at this ⊢; linarith
  have hden : 1 / (1 - 2 * Real.exp (-40.5)) ≤ 1 + 1.1e-17 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hup : psiR x ≤ x + 2.1e-14 * x := by
    have hnum : Real.exp (δ ^ 2 / 2 + 1.26e-14) * x + (14990 * √x + 7.6e-15 * x + 1e-17 * x + 1.82e12) ≤
        (1 + 1.2602e-14) * x + (14990 * √x + 7.6e-15 * x + 1e-17 * x + 1.82e12) := by
      have := mul_le_mul_of_nonneg_right hexp1 hx0.le; linarith
    have hnum0 : 0 ≤ (1 + 1.2602e-14) * x + (14990 * √x + 7.6e-15 * x + 1e-17 * x + 1.82e12) := by positivity
    have hq : (Real.exp (δ ^ 2 / 2 + 1.26e-14) * x + (14990 * √x + 7.6e-15 * x + 1e-17 * x + 1.82e12)) /
        (1 - 2 * Real.exp (-40.5)) ≤
        ((1 + 1.2602e-14) * x + (14990 * √x + 7.6e-15 * x + 1e-17 * x + 1.82e12)) * (1 + 1.1e-17) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum hden (by apply div_nonneg zero_le_one; linarith) hnum0
    have h4 : 4 * (1e10 * Real.exp (1.26e-14)) ≤ 4.0001e10 := by nlinarith
    nlinarith
  -- lower
  have hb : Real.log (1e10 / x) ≤ -(9 * δ) := by rw [hKd]; exact hb0
  have hEl := hErr (-(9 * δ)) (by rw [hKd, abs_neg, abs_of_pos (by norm_num)]) hb
  have hL := psi_lower_of_err (δ := δ) (K := 9) (y0 := 1e10) (x := x) hδ0 (by norm_num)
    (by rw [hδ]; norm_num) (by norm_num) hx1.le hb hEl
  rw [hK2, hKd] at hL
  have hexp3 : 1 - 1.26e-14 ≤ Real.exp (-(1.26e-14)) := by
    have := Real.add_one_le_exp (-(1.26e-14 : ℝ)); linarith
  have hlo : x - 2.1e-14 * x ≤ psiR x := by
    have := mul_le_mul_of_nonneg_right hexp3 hx0.le
    have : 4 * x * Real.exp (-40.5) ≤ 4 * x * 2.6e-18 := by
      have := mul_le_mul_of_nonneg_left he405 (by positivity : (0:ℝ) ≤ 4 * x); linarith
    nlinarith
  rw [abs_le]; constructor <;> linarith

end TernaryGoldbach.Explicit
