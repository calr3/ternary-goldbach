import TernaryGoldbach.Explicit.PsiExplicit
import TernaryGoldbach.Explicit.LogNumerics

/-!
# `|ψ(x) − x| ≤ 2.15·10⁻¹¹ x + 3660 √x + 4.2·10¹⁰` for `x ≥ 10¹⁹`

`psi_upper_explicit`, `psi_lower_explicit` with `δ = 8/H`, `K₀ = 8`, `y₀ = 10¹⁰` (`H = 3·10¹²`).
-/

open Complex Set Filter MeasureTheory
open scoped Real

namespace TernaryGoldbach.Explicit

/-! ## Constants at `H = 3·10¹²` -/

theorem log_3e12_le : Real.log (3e12 + 25.48) ≤ 28.7298 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 28 (u := 0.7298) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_375e12_le : Real.log (1.25 * (3e12 + 3.48 + 11)) ≤ 28.9529 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 28 (u := 0.9529) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_375e12_le' : Real.log (1.25 * (3e12 + 11)) ≤ 28.9529 :=
  (Real.log_le_log (by norm_num) (by norm_num)).trans log_375e12_le

theorem log_3e12_le' : Real.log (3e12 + 22) ≤ 28.7298 :=
  (Real.log_le_log (by norm_num) (by norm_num)).trans log_3e12_le

theorem log_10_23_ge : 1.4696 ≤ Real.log (10 / 2.3) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound' (x := 0.4696) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have e : Real.exp 1.4696 = Real.exp 1 * Real.exp 0.4696 := by rw [← Real.exp_add]; norm_num
  rw [e]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.4696]

theorem log_10_3_ge : 1.2039 ≤ Real.log (10 / 3) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound' (x := 0.2039) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have e : Real.exp 1.2039 = Real.exp 1 * Real.exp 0.2039 := by rw [← Real.exp_add]; norm_num
  rw [e]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.2039]

theorem logBPz2_H_le : Real.log (BPz2 (3e12 + 3.48) / 0.355) ≤ 299.55 := by
  have h := log_BPz2_le' (3e12 + 3.48)
  rw [abs_of_pos (by norm_num)] at h
  have h1 : Real.log (3e12 + 3.48 + 22) ≤ 28.7298 := by
    rw [show (3e12 : ℝ) + 3.48 + 22 = 3e12 + 25.48 by norm_num]; exact log_3e12_le
  have h2 := log_375e12_le
  linarith

theorem logBPz2_H_le' : Real.log (BPz2 3e12 / 0.355) ≤ 299.55 := by
  have h := log_BPz2_le' 3e12
  rw [abs_of_pos (by norm_num)] at h
  have h1 := log_3e12_le'
  have h2 := log_375e12_le'
  linarith

theorem ZLg_H_le : ZLg BPz2 3e12 ≤ 203.9 := by
  unfold ZLg
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_23_ge)]
  have := logBPz2_H_le; have := log_10_23_ge
  nlinarith

theorem Z3g_H_le : Z3g BPz2 3e12 ≤ 248.9 := by
  unfold Z3g
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
  have := logBPz2_H_le'; have := log_10_3_ge
  nlinarith

theorem Z3g_H_nonneg : 0 ≤ Z3g BPz2 3e12 := by
  unfold Z3g
  exact div_nonneg (polyDatum_zeta2.log_pos _).le (lt_of_lt_of_le (by norm_num) log_10_3_ge).le

theorem c3g_H_le : c3g 10 3e12 ≤ 1.22e-11 := by
  unfold c3g
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
  have := log_10_3_ge
  nlinarith

theorem c3g_H_nonneg : 0 ≤ c3g 10 3e12 := by
  unfold c3g; exact div_nonneg (by norm_num) (lt_of_lt_of_le (by norm_num) log_10_3_ge).le

theorem log_Jl_H_le : Real.log (Jl 3e12) ≤ 27.49 := by
  have hJ : (Jl 3e12 : ℝ) ≤ 3e12 / 3.48 + 1 := by
    unfold Jl; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 3e12 / 3.48 by norm_num); linarith
  have hJ0 : (0:ℝ) < Jl 3e12 := by unfold Jl; positivity
  refine (Real.log_le_log hJ0 hJ).trans (log_le_of_le_exp'' (by norm_num) ?_)
  have h := exp_split_ge' 27 (u := 0.49) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

/-! ## The plateau parameters -/

theorem exp_small_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ 1 + 2 * t := by
  have := Real.exp_bound' h0 h1 (n := 1) one_pos
  norm_num [Finset.sum_range_succ] at this; linarith

theorem exp_neg32_le : Real.exp (-32) ≤ 1.3e-14 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := exp_nat_ge' 32
  norm_num at this ⊢; linarith

/-- `e^{b/2} = √(10¹⁰/x) ≤ 3.2·10⁻⁵` for `b = log(10¹⁰/x)`, `x ≥ 10¹⁹`. -/
theorem exp_half_log_le {x : ℝ} (hx : 1e19 ≤ x) : Real.exp (Real.log (1e10 / x) / 2) ≤ 3.2e-5 := by
  have hx0 : 0 < x := by linarith
  set e := Real.exp (Real.log (1e10 / x) / 2) with he
  have he0 : 0 < e := Real.exp_pos _
  have hsq : e ^ 2 = 1e10 / x := by
    rw [he, sq, ← Real.exp_add, show Real.log (1e10 / x) / 2 + Real.log (1e10 / x) / 2 =
      Real.log (1e10 / x) by ring, Real.exp_log (by positivity)]
  have hq : 1e10 / x ≤ 1e-9 := by rw [div_le_iff₀ hx0]; linarith
  nlinarith

theorem log_10_336_ge : 1.0906 ≤ Real.log (10 / 3.36) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound' (x := 0.0906) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have e : Real.exp 1.0906 = Real.exp 1 * Real.exp 0.0906 := by rw [← Real.exp_add]; norm_num
  rw [e]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.0906]

theorem logBPz2_H6_le : Real.log (BPz2 (3e12 + 6) / 0.355) ≤ 299.55 := by
  have h := log_BPz2_le' (3e12 + 6)
  rw [abs_of_pos (by norm_num)] at h
  have h1 : Real.log (3e12 + 6 + 22) ≤ 28.7298 := by
    refine log_le_of_le_exp'' (by norm_num) ?_
    have h := exp_split_ge' 28 (u := 0.7298) (by norm_num) 10
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith
  have h2 : Real.log (1.25 * (3e12 + 6 + 11)) ≤ 28.9529 := by
    refine log_le_of_le_exp'' (by norm_num) ?_
    have h := exp_split_ge' 28 (u := 0.9529) (by norm_num) 12
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith
  linarith

theorem ZLh_H_le : ZLh 6 3.36 3e12 ≤ 274.7 := by
  unfold ZLh
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_336_ge)]
  have := logBPz2_H6_le; have := log_10_336_ge
  nlinarith

theorem log_JlH_H_le : Real.log (JlH 6 3e12) ≤ 26.94 := by
  have hJ : (JlH 6 3e12 : ℝ) ≤ 3e12 / 6 + 1 := by
    unfold JlH; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 3e12 / 6 by norm_num); linarith
  have hJ0 : (0:ℝ) < JlH 6 3e12 := by unfold JlH; positivity
  refine (Real.log_le_log hJ0 hJ).trans (log_le_of_le_exp'' (by norm_num) ?_)
  have h := exp_split_ge' 26 (u := 0.94) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem LineB2_plateau_le {a x : ℝ} (ha : |a| ≤ 64 / 3e12) (hx : 1e19 ≤ x) :
    LineB2 a (Real.log (1e10 / x)) (8 / 3e12) ≤ 3658 := by
  unfold LineB2
  have he1 : Real.exp ((8 / 3e12 : ℝ) ^ 2 / 2) ≤ 1.000001 := by
    have h := exp_small_le (t := (8 / 3e12 : ℝ) ^ 2 / 2) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have he2 : Real.exp (a / 2) ≤ 1.000001 := by
    have h1 : a / 2 ≤ |a| := by cases abs_cases a <;> linarith
    have h := exp_small_le (t := |a|) (abs_nonneg a) (by norm_num at ha ⊢; linarith)
    have := Real.exp_le_exp.2 h1
    norm_num at ha h ⊢; linarith
  have he3 := exp_half_log_le hx
  have h1 := ZLh_H_le
  have h2 := log_JlH_H_le
  have hZ0 : 0 ≤ ZLh 6 3.36 3e12 := ZLh_nonneg (by norm_num) (by norm_num)
  have hJ0 : 0 ≤ Real.log (JlH 6 3e12) := Real.log_nonneg (by unfold JlH; norm_num)
  calc ZLh 6 3.36 3e12 * (Real.exp ((8 / 3e12 : ℝ) ^ 2 / 2) *
        (Real.exp (a / 2) + Real.exp (Real.log (1e10 / x) / 2))) *
        (4 + 2 * (1 + Real.log (JlH 6 3e12)) / 6)
      ≤ 274.7 * (1.000001 * (1.000001 + 3.2e-5)) * (4 + 2 * (1 + 26.94) / 6) := by gcongr
    _ ≤ 3658 := by norm_num

theorem TailB_plateau_le {a : ℝ} (ha : |a| ≤ 64 / 3e12) : TailB a (8 / 3e12) ≤ 1e-13 := by
  unfold TailB EBg rhoG
  set t : ℝ := 4.4 * (8 / 3e12) ^ 2 * 3e12 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have h1r : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have h := Real.add_one_le_exp t
    rw [Real.exp_neg]
    have hp : 0 < Real.exp t := Real.exp_pos t
    rw [div_le_iff₀ (by linarith), sub_mul, one_mul, inv_mul_eq_div]
    have : (1 + t) / Real.exp t ≤ 1 := by rw [div_le_one hp]; linarith
    linarith
  have htv : (9.38e-11 : ℝ) ≤ t / (1 + t) := by
    rw [le_div_iff₀ (by linarith), ht]; norm_num
  have hr : (9.38e-11 : ℝ) ≤ 1 - Real.exp (-t) := htv.trans h1r
  have he : Real.exp ((8 / 3e12 : ℝ) ^ 2 / 2 + |a|) ≤ 1.000001 := by
    have h := exp_small_le (t := (8 / 3e12 : ℝ) ^ 2 / 2 + |a|) (by positivity) (by norm_num at ha ⊢; linarith)
    norm_num at ha h ⊢; linarith
  have hg : Real.exp (-((8 / 3e12 : ℝ) ^ 2 * (3e12 : ℝ) ^ 2 / 2)) ≤ 1.3e-14 := by
    rw [show (8 / 3e12 : ℝ) ^ 2 * (3e12 : ℝ) ^ 2 / 2 = 32 by norm_num]; exact exp_neg32_le
  have hZ := Z3g_H_le; have hZ0 := Z3g_H_nonneg
  have hc := c3g_H_le; have hc0 := c3g_H_nonneg
  have hr0 : 0 < 1 - Real.exp (-t) := lt_of_lt_of_le (by norm_num) hr
  have hA : 2 * Z3g BPz2 3e12 / (1 - Real.exp (-t)) ≤ 2 * 248.9 / 9.38e-11 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hB : 2 * c3g 10 3e12 / (1 - Real.exp (-t)) ^ 2 ≤ 2 * 1.22e-11 / (9.38e-11) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (9.38e-11 : ℝ) ^ 2 ≤ (1 - Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (by norm_num) hr 2
    nlinarith
  have hE0 : 0 ≤ 2 * Real.exp ((8 / 3e12 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((8 / 3e12 : ℝ) ^ 2 * (3e12 : ℝ) ^ 2 / 2)) / 3e12 := by
    positivity
  have hE : 2 * Real.exp ((8 / 3e12 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((8 / 3e12 : ℝ) ^ 2 * (3e12 : ℝ) ^ 2 / 2)) / 3e12 ≤
      2 * 1.000001 * 1.3e-14 / 3e12 := by gcongr
  have hS0 : 0 ≤ 2 * Z3g BPz2 3e12 / (1 - Real.exp (-t)) + 2 * c3g 10 3e12 / (1 - Real.exp (-t)) ^ 2 := by positivity
  calc 2 * Real.exp ((8 / 3e12 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((8 / 3e12 : ℝ) ^ 2 * (3e12 : ℝ) ^ 2 / 2)) / 3e12 *
        (2 * Z3g BPz2 3e12 / (1 - Real.exp (-t)) + 2 * c3g 10 3e12 / (1 - Real.exp (-t)) ^ 2)
      ≤ (2 * 1.000001 * 1.3e-14 / 3e12) * (2 * 248.9 / 9.38e-11 + 2 * 1.22e-11 / (9.38e-11) ^ 2) :=
        mul_le_mul hE (add_le_add hA hB) hS0 (by norm_num)
    _ ≤ 1e-13 := by norm_num

theorem Vg_plateau_le {a x : ℝ} (ha : |a| ≤ 64 / 3e12) (hx : 1e19 ≤ x) :
    x ^ (-(1 / 2) : ℝ) * Vg a (Real.log (1e10 / x)) (8 / 3e12) / (2 * π) ≤ 9.6e8 := by
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
  have hδe : Real.exp ((8 / 3e12 : ℝ) ^ 2 / 8) ≤ 1.000001 := by
    have h := exp_small_le (t := (8 / 3e12 : ℝ) ^ 2 / 8) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have hae : Real.exp (-(a / 2)) ≤ 1.000001 := by
    have h1 : -(a / 2) ≤ |a| := by cases abs_cases a <;> linarith
    have h := exp_small_le (t := |a|) (abs_nonneg a) (by norm_num at ha ⊢; linarith)
    have := Real.exp_le_exp.2 h1
    norm_num at ha h ⊢; linarith
  have hpi : 2.5066 ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have := Real.pi_gt_d6; nlinarith
  have hpi0 : 0 < √(2 * π) := by linarith
  unfold Vg
  rw [hsx, hb]
  set c₁ := 2 / Real.log 2 + 4.8
  set E := Real.exp ((8 / 3e12 : ℝ) ^ 2 / 8)
  set A := Real.exp (-(a / 2))
  set P := √(2 * π) with hP
  have hP2 : P * P = 2 * π := Real.mul_self_sqrt (by positivity)
  have e : 1 / √x * (c₁ * 82.6 * E * (A + √x / 1e5) * (P / (8 / 3e12))) / (2 * π) =
      (c₁ * 82.6 * E * 3.75e11) * (1 / P) * (A / √x + 1e-5) := by
    rw [← hP2]
    field_simp
    ring
  rw [e]
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have h1 : c₁ * 82.6 * E * 3.75e11 ≤ 7.6856 * 82.6 * 1.000001 * 3.75e11 := by gcongr
  have h2 : 1 / √(2 * π) ≤ 1 / 2.5066 := one_div_le_one_div_of_le (by norm_num) hpi
  have h3 : A / √x + 1e-5 ≤ 1.000001 / 3.16e9 + 1e-5 := by
    have : A / √x ≤ 1.000001 / 3.16e9 := div_le_div₀ (by norm_num) hae (by norm_num) hS
    linarith
  calc (c₁ * 82.6 * E * 3.75e11) * (1 / √(2 * π)) * (A / √x + 1e-5)
      ≤ (7.6856 * 82.6 * 1.000001 * 3.75e11) * (1 / 2.5066) * (1.000001 / 3.16e9 + 1e-5) := by
        gcongr
    _ ≤ 9.6e8 := by norm_num

theorem exp_small_le2 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ 1 + t + t ^ 2 := by
  have := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  nlinarith [sq_nonneg t]

theorem ErrG_plateau_le {a x : ℝ} (ha : |a| ≤ 64 / 3e12) (hx : 1e19 ≤ x) :
    ErrG a (Real.log (1e10 / x)) (8 / 3e12) x ≤ 3658 * √x + 1e-13 * x + 9.6e8 := by
  unfold ErrG
  have h1 := LineB2_plateau_le ha hx
  have h2 := TailB_plateau_le ha
  have h3 := Vg_plateau_le ha hx
  have hx0 : 0 ≤ x := by linarith
  have := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
  have := mul_le_mul_of_nonneg_left h2 hx0
  nlinarith

/-- **`|ψ(x) − x| ≤ 2.15·10⁻¹¹ x + 3660 √x + 4.2·10¹⁰`** for `x ≥ 10¹⁹`. -/
theorem psi_plateau {x : ℝ} (hx : 1e19 ≤ x) : |psiR x - x| ≤ 2.15e-11 * x + 3660 * √x + 4.2e10 := by
  have hx0 : 0 < x := by linarith
  set δ : ℝ := 8 / 3e12 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hKd : (8 : ℝ) * δ = 64 / 3e12 := by rw [hδ]; norm_num
  have hK2 : -((8 : ℝ) ^ 2 / 2) = -32 := by norm_num
  have he32 := exp_neg32_le
  have he32' : 0 < Real.exp (-32) := Real.exp_pos _
  have hsx := Real.sqrt_nonneg x
  -- upper
  have hK1 : 2 * Real.exp (-((8 : ℝ) ^ 2 / 2)) < 1 := by rw [hK2]; linarith
  have hYx : 1e10 * Real.exp (8 * δ) ≤ x := by
    rw [hKd]
    have := exp_small_le (t := (64 / 3e12 : ℝ)) (by norm_num) (by norm_num)
    nlinarith
  have hU := psi_upper_explicit (δ := δ) (K := 8) (y0 := 1e10) (x := x) hδ0 (by norm_num)
    hK1 (by norm_num) (by linarith) hYx
  rw [hK2, hKd] at hU
  have hEu := ErrG_plateau_le (a := 64 / 3e12) (by rw [abs_of_pos (by norm_num)]) hx
  rw [← hKd] at hEu
  rw [hKd] at hEu
  have hexp1 : Real.exp (δ ^ 2 / 2 + 64 / 3e12) ≤ 1 + 2.1334e-11 := by
    have h := exp_small_le2 (t := δ ^ 2 / 2 + 64 / 3e12) (by positivity) (by rw [hδ]; norm_num)
    rw [hδ] at h ⊢; norm_num at h ⊢; linarith
  have hexp2 : Real.exp (64 / 3e12) ≤ 1.0000001 := by
    have := exp_small_le (t := (64 / 3e12 : ℝ)) (by norm_num) (by norm_num); norm_num at this ⊢; linarith
  have hden : 1 / (1 - 2 * Real.exp (-32)) ≤ 1 + 3e-14 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hup : psiR x ≤ x + 2.15e-11 * x + 3660 * √x + 4.2e10 := by
    have hnum : Real.exp (δ ^ 2 / 2 + 64 / 3e12) * x + ErrG (64 / 3e12) (Real.log (1e10 / x)) δ x ≤
        (1 + 2.1334e-11) * x + (3658 * √x + 1e-13 * x + 9.6e8) := by
      have := mul_le_mul_of_nonneg_right hexp1 hx0.le; linarith
    have hnum0 : 0 ≤ (1 + 2.1334e-11) * x + (3658 * √x + 1e-13 * x + 9.6e8) := by positivity
    have hd0 : 0 < 1 - 2 * Real.exp (-32) := by linarith
    have hq : (Real.exp (δ ^ 2 / 2 + 64 / 3e12) * x + ErrG (64 / 3e12) (Real.log (1e10 / x)) δ x) /
        (1 - 2 * Real.exp (-32)) ≤ ((1 + 2.1334e-11) * x + (3658 * √x + 1e-13 * x + 9.6e8)) * (1 + 3e-14) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum hden (by positivity) hnum0
    have h4 : 4 * (1e10 * Real.exp (64 / 3e12)) ≤ 4.0001e10 := by nlinarith
    nlinarith
  -- lower
  have hb : Real.log (1e10 / x) ≤ -(8 * δ) := by
    rw [hKd]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1e10 / x by positivity)
    have : 1e10 / x ≤ 1e-9 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  have hL := psi_lower_explicit (δ := δ) (K := 8) (y0 := 1e10) (x := x) hδ0 (by rw [hδ]; norm_num)
    (by rw [hδ]; norm_num) (by norm_num) (by linarith) hb
  rw [hK2, hKd] at hL
  have hEl := ErrG_plateau_le (a := -(64 / 3e12)) (by rw [abs_neg, abs_of_pos (by norm_num)]) hx
  have hexp3 : 1 - 64 / 3e12 ≤ Real.exp (-(64 / 3e12)) := by
    have := Real.add_one_le_exp (-(64 / 3e12 : ℝ)); linarith
  have hlo : x - 2.15e-11 * x - 3660 * √x - 4.2e10 ≤ psiR x := by
    have := mul_le_mul_of_nonneg_right hexp3 hx0.le
    have : 4 * x * Real.exp (-32) ≤ 4 * x * 1.3e-14 := by
      have := mul_le_mul_of_nonneg_left he32 (by positivity : (0:ℝ) ≤ 4 * x); linarith
    nlinarith
  rw [abs_le]; constructor <;> linarith

end TernaryGoldbach.Explicit
