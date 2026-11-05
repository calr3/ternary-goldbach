import TernaryGoldbach.Explicit.PsiExplicit
import TernaryGoldbach.Explicit.LogNumerics

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# `|ψ(x) − x| ≤ 1.82·10⁻⁹ x + 1145 √x + 4.2·10¹⁰` for `x ≥ 10¹⁷`

`psi_upper_explicit`, `psi_lower_explicit` with `δ = 7/H`, `K₀ = 7`, `y₀ = 10¹⁰` (`H = 3·10¹⁰`).
-/

open Complex Set Filter MeasureTheory
open scoped Real

namespace TernaryGoldbach.Explicit

/-! ## Constants at `H = 3·10¹⁰` -/

theorem log_3e10_le : Real.log (3e10 + 25.48) ≤ 24.1245 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 24 (u := 0.1245) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_375e12_le : Real.log (1.25 * (3e10 + 3.48 + 11)) ≤ 24.3477 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 24 (u := 0.3477) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_375e12_le' : Real.log (1.25 * (3e10 + 11)) ≤ 24.3477 :=
  (Real.log_le_log (by norm_num) (by norm_num)).trans log_375e12_le

theorem log_3e10_le' : Real.log (3e10 + 22) ≤ 24.1245 :=
  (Real.log_le_log (by norm_num) (by norm_num)).trans log_3e10_le

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

theorem logBPz2_H_le : Real.log (BPz2 (3e10 + 3.48) / 0.355) ≤ 253.5 := by
  have h := log_BPz2_le' (3e10 + 3.48)
  rw [abs_of_pos (by norm_num)] at h
  have h1 : Real.log (3e10 + 3.48 + 22) ≤ 24.1245 := by
    rw [show (3e10 : ℝ) + 3.48 + 22 = 3e10 + 25.48 by norm_num]; exact log_3e10_le
  have h2 := log_375e12_le
  linarith

theorem logBPz2_H_le' : Real.log (BPz2 3e10 / 0.355) ≤ 253.5 := by
  have h := log_BPz2_le' 3e10
  rw [abs_of_pos (by norm_num)] at h
  have h1 := log_3e10_le'
  have h2 := log_375e12_le'
  linarith

theorem ZLg_H_le : ZLg BPz2 3e10 ≤ 172.6 := by
  unfold ZLg
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_23_ge)]
  have := logBPz2_H_le; have := log_10_23_ge
  nlinarith

theorem Z3g_H_le : Z3g BPz2 3e10 ≤ 210.6 := by
  unfold Z3g
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
  have := logBPz2_H_le'; have := log_10_3_ge
  nlinarith

theorem Z3g_H_nonneg : 0 ≤ Z3g BPz2 3e10 := by
  unfold Z3g
  exact div_nonneg (polyDatum_zeta2.log_pos _).le (lt_of_lt_of_le (by norm_num) log_10_3_ge).le

theorem c3g_H_le : c3g 10 3e10 ≤ 1.22e-9 := by
  unfold c3g
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) log_10_3_ge)]
  have := log_10_3_ge
  nlinarith

theorem c3g_H_nonneg : 0 ≤ c3g 10 3e10 := by
  unfold c3g; exact div_nonneg (by norm_num) (lt_of_lt_of_le (by norm_num) log_10_3_ge).le

theorem log_Jl_H_le : Real.log (Jl 3e10) ≤ 22.88 := by
  have hJ : (Jl 3e10 : ℝ) ≤ 3e10 / 3.48 + 1 := by
    unfold Jl; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 3e10 / 3.48 by norm_num); linarith
  have hJ0 : (0:ℝ) < Jl 3e10 := by unfold Jl; positivity
  refine (Real.log_le_log hJ0 hJ).trans (log_le_of_le_exp'' (by norm_num) ?_)
  have h := exp_split_ge' 22 (u := 0.88) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

/-! ## The plateau parameters -/

theorem exp_small_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ 1 + 2 * t := by
  have := Real.exp_bound' h0 h1 (n := 1) one_pos
  norm_num [Finset.sum_range_succ] at this; linarith

theorem exp_neg245_le : Real.exp (-24.5) ≤ 2.31e-11 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have h := exp_split_ge' 24 (u := 0.5) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem exp_neg32_le : Real.exp (-32) ≤ 1.3e-14 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := exp_nat_ge' 32
  norm_num at this ⊢; linarith

/-- `e^{b/2} = √(10¹⁰/x) ≤ 3.17·10⁻⁴` for `b = log(10¹⁰/x)`, `x ≥ 10¹⁷`. -/
theorem exp_half_log_le {x : ℝ} (hx : 1e17 ≤ x) : Real.exp (Real.log (1e10 / x) / 2) ≤ 3.17e-4 := by
  have hx0 : 0 < x := by linarith
  set e := Real.exp (Real.log (1e10 / x) / 2) with he
  have he0 : 0 < e := Real.exp_pos _
  have hsq : e ^ 2 = 1e10 / x := by
    rw [he, sq, ← Real.exp_add, show Real.log (1e10 / x) / 2 + Real.log (1e10 / x) / 2 =
      Real.log (1e10 / x) by ring, Real.exp_log (by positivity)]
  have hq : 1e10 / x ≤ 1e-7 := by rw [div_le_iff₀ hx0]; linarith
  nlinarith

theorem log_10_336_ge : 1.0906 ≤ Real.log (10 / 3.36) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound' (x := 0.0906) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have e : Real.exp 1.0906 = Real.exp 1 * Real.exp 0.0906 := by rw [← Real.exp_add]; norm_num
  rw [e]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.0906]

theorem log_JlH_H_le : Real.log (JlH 6 3e10) ≤ 22.34 := by
  have hJ : (JlH 6 3e10 : ℝ) ≤ 3e10 / 6 + 1 := by
    unfold JlH; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 3e10 / 6 by norm_num); linarith
  have hJ0 : (0:ℝ) < JlH 6 3e10 := by unfold JlH; positivity
  refine (Real.log_le_log hJ0 hJ).trans (log_le_of_le_exp'' (by norm_num) ?_)
  have h := exp_split_ge' 22 (u := 0.34) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem logBPz2_3_le : Real.log (BPz2 3 / 0.355) ≤ 39.15 := by
  refine log_le_of_le_exp'' (by unfold BPz2; positivity) ?_
  have h := exp_split_ge' 39 (u := 0.15) (by norm_num) 10
  unfold BPz2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- `log(αd + β) ≤ log α + log d + β/(αd)`. -/
theorem log_affine_le {α β d : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hd : 0 < d) :
    Real.log (α * d + β) ≤ Real.log α + Real.log d + β / (α * d) := by
  have had : 0 < α * d := mul_pos hα hd
  have h1 : Real.log (α * d + β) = Real.log (α * d) + Real.log ((α * d + β) / (α * d)) := by
    rw [Real.log_div (by positivity) had.ne']; ring
  have h2 := Real.log_le_sub_one_of_pos (show 0 < (α * d + β) / (α * d) by positivity)
  have h3 : (α * d + β) / (α * d) - 1 = β / (α * d) := by field_simp; ring
  rw [h1, Real.log_mul hα.ne' hd.ne']
  linarith

theorem log_6_le : Real.log 6 ≤ 1.7918 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 1 (u := 0.7918) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log_75_le : Real.log 7.5 ≤ 2.015 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 2 (u := 0.015) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

/-- Jensen for the window at distance `d = m + 1` (centre `6d + 3`):
`log(B(6d + 3)/0.355) ≤ 30.17 + 10 log d + 25.17/d`. -/
theorem logB_window_le (m : ℕ) :
    Real.log (BPz2 ((((m + 1 : ℕ) : ℝ) + 1 / 2) * 6) / 0.355) ≤
      30.17 + 10 * Real.log ((m : ℝ) + 1) + 25.17 / ((m : ℝ) + 1) := by
  have hm := (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  set d : ℝ := (m : ℝ) + 1 with hd
  have hd0 : 0 < d := by linarith
  have hT : (((m + 1 : ℕ) : ℝ) + 1 / 2) * 6 = 6 * d + 3 := by rw [hd]; push_cast; ring
  rw [hT]
  have h := log_BPz2_le' (6 * d + 3)
  rw [abs_of_pos (by linarith)] at h
  have e1 : 6 * d + 3 + 22 = 6 * d + 25 := by ring
  have e2 : 1.25 * (6 * d + 3 + 11) = 7.5 * d + 17.5 := by ring
  rw [e1, e2] at h
  have h1 := log_affine_le (α := 6) (β := 25) (by norm_num) (by norm_num) hd0
  have h2 := log_affine_le (α := 7.5) (β := 17.5) (by norm_num) (by norm_num) hd0
  have h6 := log_6_le
  have h75 := log_75_le
  have hi : 0 < 1 / d := by positivity
  have e3 : (25 : ℝ) / (6 * d) = 25 / 6 * (1 / d) := by rw [mul_one_div, div_div]
  have e4 : (17.5 : ℝ) / (7.5 * d) = 17.5 / 7.5 * (1 / d) := by rw [mul_one_div, div_div]
  have e5 : (25.17 : ℝ) / d = 25.17 * (1 / d) := by rw [mul_one_div]
  rw [e3] at h1
  rw [e4] at h2
  rw [e5]
  linarith

/-- The weighted window sum of `line_sum_leH` at `h = 6`, `r = 3.36`, `H = 3·10¹²`. -/
theorem window_sum_le :
    ∑ m ∈ Finset.range (JlH 6 3e10), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ))) ≤ 571 := by
  have hJ1 : 1 ≤ JlH 6 3e10 := by unfold JlH; omega
  obtain ⟨k, hk⟩ : ∃ k, JlH 6 3e10 = k + 1 := ⟨JlH 6 3e10 - 1, by omega⟩
  have hlogk : Real.log (k : ℝ) ≤ 22.34 := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]; norm_num
    · refine le_trans (Real.log_le_log (by exact_mod_cast h0) ?_) log_JlH_H_le
      rw [hk]; push_cast; linarith
  have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hL := log_10_336_ge
  have hL0 : 0 < Real.log (10 / 3.36) := lt_of_lt_of_le (by norm_num) hL
  rw [hk, Finset.sum_range_succ']
  -- the two windows next to the real axis (centre `±3`)
  have h0 : Real.log (BPz2 ((((0 : ℕ) : ℝ) + 1 / 2) * 6) / 0.355) / Real.log (10 / 3.36) *
      (1 / max (1 / 2 : ℝ) (6 * ((0 : ℕ) : ℝ))) ≤ 39.15 / 1.0906 * 2 := by
    have e : (((0 : ℕ) : ℝ) + 1 / 2) * 6 = 3 := by norm_num
    have e2 : (1 : ℝ) / max (1 / 2) (6 * ((0 : ℕ) : ℝ)) = 2 := by
      rw [Nat.cast_zero, mul_zero, max_eq_left (by norm_num)]; norm_num
    rw [e, e2]
    have h3 := logBPz2_3_le
    have hpos := (polyDatum_zeta2.log_pos 3).le
    have : Real.log (BPz2 3 / 0.355) / Real.log (10 / 3.36) ≤ 39.15 / 1.0906 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; nlinarith
    linarith
  -- the windows at distance `d = m + 1 ≥ 1`
  have hterm : ∀ m ∈ Finset.range k, Real.log (BPz2 ((((m + 1 : ℕ) : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * ((m + 1 : ℕ) : ℝ))) ≤
      1 / (6 * 1.0906) * ((30.17 + 10 * Real.log ((m : ℝ) + 1)) / ((m : ℝ) + 1) +
        25.17 * (1 / ((m : ℝ) + 1) ^ 2)) := by
    intro m _
    have hm := (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have hw := logB_window_le m
    have hpos := (polyDatum_zeta2.log_pos ((((m + 1 : ℕ) : ℝ) + 1 / 2) * 6)).le
    have hmax : max (1 / 2 : ℝ) (6 * ((m + 1 : ℕ) : ℝ)) = 6 * ((m : ℝ) + 1) := by
      push_cast; exact max_eq_right (by linarith)
    rw [hmax]
    set X := Real.log (BPz2 ((((m + 1 : ℕ) : ℝ) + 1 / 2) * 6) / 0.355) with hX
    set d : ℝ := (m : ℝ) + 1 with hdd
    have hd0 : 0 < d := by linarith
    have hXL : X / Real.log (10 / 3.36) ≤ X / 1.0906 :=
      div_le_div_of_nonneg_left hpos (by norm_num) hL
    have e : (30.17 + 10 * Real.log d) / d + 25.17 * (1 / d ^ 2) =
        (30.17 + 10 * Real.log d + 25.17 / d) / d := by
      field_simp
    rw [e]
    calc X / Real.log (10 / 3.36) * (1 / (6 * d)) ≤ X / 1.0906 * (1 / (6 * d)) :=
          mul_le_mul_of_nonneg_right hXL (by positivity)
      _ ≤ (30.17 + 10 * Real.log d + 25.17 / d) / 1.0906 * (1 / (6 * d)) := by gcongr
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hA := sum_log_div_le (a := 30.17) (b := 10) (by norm_num) (by norm_num) k
  have hB := sum_inv_sq_le_two k
  have hsq : Real.log (k : ℝ) ^ 2 ≤ 22.34 ^ 2 := pow_le_pow_left₀ hlogk0 hlogk 2
  linarith

theorem LineB2_plateau_le {a x : ℝ} (ha : |a| ≤ 49 / 3e10) (hx : 1e17 ≤ x) :
    LineB2 a (Real.log (1e10 / x)) (7 / 3e10) ≤ 1143 := by
  unfold LineB2
  have he1 : Real.exp ((7 / 3e10 : ℝ) ^ 2 / 2) ≤ 1.000001 := by
    have h := exp_small_le (t := (7 / 3e10 : ℝ) ^ 2 / 2) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have he2 : Real.exp (a / 2) ≤ 1.000001 := by
    have h1 : a / 2 ≤ |a| := by cases abs_cases a <;> linarith
    have h := exp_small_le (t := |a|) (abs_nonneg a) (by norm_num at ha ⊢; linarith)
    have := Real.exp_le_exp.2 h1
    norm_num at ha h ⊢; linarith
  have he3 := exp_half_log_le hx
  have hS := window_sum_le
  have hS0 : 0 ≤ ∑ m ∈ Finset.range (JlH 6 3e10), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ))) :=
    Finset.sum_nonneg fun m _ => mul_nonneg
      (div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le)
      (one_div_nonneg.2 (le_trans (by norm_num) (le_max_left _ _)))
  calc (Real.exp ((7 / 3e10 : ℝ) ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (Real.log (1e10 / x) / 2))) *
        (2 * ∑ m ∈ Finset.range (JlH 6 3e10), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
          Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ))))
      ≤ (1.000001 * (1.000001 + 3.17e-4)) * (2 * 571) := by gcongr
    _ ≤ 1143 := by norm_num

theorem TailB_plateau_le {a : ℝ} (ha : |a| ≤ 49 / 3e10) : TailB a (7 / 3e10) ≤ 9.1e-11 := by
  unfold TailB EBg rhoG
  set t : ℝ := 4.4 * (7 / 3e10) ^ 2 * 3e10 with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have h1r : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have h := Real.add_one_le_exp t
    rw [Real.exp_neg]
    have hp : 0 < Real.exp t := Real.exp_pos t
    rw [div_le_iff₀ (by linarith), sub_mul, one_mul, inv_mul_eq_div]
    have : (1 + t) / Real.exp t ≤ 1 := by rw [div_le_one hp]; linarith
    linarith
  have htv : (7.18e-9 : ℝ) ≤ t / (1 + t) := by
    rw [le_div_iff₀ (by linarith), ht]; norm_num
  have hr : (7.18e-9 : ℝ) ≤ 1 - Real.exp (-t) := htv.trans h1r
  have he : Real.exp ((7 / 3e10 : ℝ) ^ 2 / 2 + |a|) ≤ 1.000001 := by
    have h := exp_small_le (t := (7 / 3e10 : ℝ) ^ 2 / 2 + |a|) (by positivity) (by norm_num at ha ⊢; linarith)
    norm_num at ha h ⊢; linarith
  have hg : Real.exp (-((7 / 3e10 : ℝ) ^ 2 * (3e10 : ℝ) ^ 2 / 2)) ≤ 2.31e-11 := by
    rw [show (7 / 3e10 : ℝ) ^ 2 * (3e10 : ℝ) ^ 2 / 2 = 24.5 by norm_num]; exact exp_neg245_le
  have hZ := Z3g_H_le; have hZ0 := Z3g_H_nonneg
  have hc := c3g_H_le; have hc0 := c3g_H_nonneg
  have hr0 : 0 < 1 - Real.exp (-t) := lt_of_lt_of_le (by norm_num) hr
  have hA : 2 * Z3g BPz2 3e10 / (1 - Real.exp (-t)) ≤ 2 * 210.6 / 7.18e-9 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hB : 2 * c3g 10 3e10 / (1 - Real.exp (-t)) ^ 2 ≤ 2 * 1.22e-9 / (7.18e-9) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (7.18e-9 : ℝ) ^ 2 ≤ (1 - Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (by norm_num) hr 2
    nlinarith
  have hE0 : 0 ≤ 2 * Real.exp ((7 / 3e10 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((7 / 3e10 : ℝ) ^ 2 * (3e10 : ℝ) ^ 2 / 2)) / 3e10 := by
    positivity
  have hE : 2 * Real.exp ((7 / 3e10 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((7 / 3e10 : ℝ) ^ 2 * (3e10 : ℝ) ^ 2 / 2)) / 3e10 ≤
      2 * 1.000001 * 2.31e-11 / 3e10 := by gcongr
  have hS0 : 0 ≤ 2 * Z3g BPz2 3e10 / (1 - Real.exp (-t)) + 2 * c3g 10 3e10 / (1 - Real.exp (-t)) ^ 2 := by positivity
  calc 2 * Real.exp ((7 / 3e10 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((7 / 3e10 : ℝ) ^ 2 * (3e10 : ℝ) ^ 2 / 2)) / 3e10 *
        (2 * Z3g BPz2 3e10 / (1 - Real.exp (-t)) + 2 * c3g 10 3e10 / (1 - Real.exp (-t)) ^ 2)
      ≤ (2 * 1.000001 * 2.31e-11 / 3e10) * (2 * 210.6 / 7.18e-9 + 2 * 1.22e-9 / (7.18e-9) ^ 2) :=
        mul_le_mul hE (add_le_add hA hB) hS0 (by norm_num)
    _ ≤ 9.1e-11 := by norm_num

theorem Vg_plateau_le {a x : ℝ} (ha : |a| ≤ 49 / 3e10) (hx : 1e17 ≤ x) :
    x ^ (-(1 / 2) : ℝ) * Vg a (Real.log (1e10 / x)) (7 / 3e10) / (2 * π) ≤ 1.09e7 := by
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
  have hS : 3.16e8 ≤ √x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]; norm_num; linarith
  have hS0 : 0 < √x := by linarith
  have hc1 : 2 / Real.log 2 + 4.8 ≤ 7.6856 := by
    have := Real.log_two_gt_d9
    have : 2 / Real.log 2 ≤ 2 / 0.6931 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have : (2 : ℝ) / 0.6931 ≤ 2.8856 := by norm_num
    linarith
  have hc10 : 0 ≤ 2 / Real.log 2 + 4.8 := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  have hδe : Real.exp ((7 / 3e10 : ℝ) ^ 2 / 8) ≤ 1.000001 := by
    have h := exp_small_le (t := (7 / 3e10 : ℝ) ^ 2 / 8) (by positivity) (by norm_num)
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
  set E := Real.exp ((7 / 3e10 : ℝ) ^ 2 / 8)
  set A := Real.exp (-(a / 2))
  set P := √(2 * π) with hP
  have hP2 : P * P = 2 * π := Real.mul_self_sqrt (by positivity)
  have e : 1 / √x * (c₁ * 82.6 * E * (A + √x / 1e5) * (P / (7 / 3e10))) / (2 * π) =
      (c₁ * 82.6 * E * (3e10 / 7)) * (1 / P) * (A / √x + 1e-5) := by
    rw [← hP2]
    field_simp
    ring
  rw [e]
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have h1 : c₁ * 82.6 * E * (3e10 / 7) ≤ 7.6856 * 82.6 * 1.000001 * (3e10 / 7) := by gcongr
  have h2 : 1 / √(2 * π) ≤ 1 / 2.5066 := one_div_le_one_div_of_le (by norm_num) hpi
  have h3 : A / √x + 1e-5 ≤ 1.000001 / 3.16e8 + 1e-5 := by
    have : A / √x ≤ 1.000001 / 3.16e8 := div_le_div₀ (by norm_num) hae (by norm_num) hS
    linarith
  calc (c₁ * 82.6 * E * (3e10 / 7)) * (1 / √(2 * π)) * (A / √x + 1e-5)
      ≤ (7.6856 * 82.6 * 1.000001 * (3e10 / 7)) * (1 / 2.5066) * (1.000001 / 3.16e8 + 1e-5) := by
        gcongr
    _ ≤ 1.09e7 := by norm_num

theorem exp_small_le2 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ 1 + t + t ^ 2 := by
  have := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  nlinarith [sq_nonneg t]

theorem ErrG_plateau_le {a x : ℝ} (ha : |a| ≤ 49 / 3e10) (hx : 1e17 ≤ x) :
    ErrG a (Real.log (1e10 / x)) (7 / 3e10) x ≤ 1143 * √x + 9.1e-11 * x + 1.09e7 := by
  unfold ErrG
  have h1 := LineB2_plateau_le ha hx
  have h2 := TailB_plateau_le ha
  have h3 := Vg_plateau_le ha hx
  have hx0 : 0 ≤ x := by linarith
  have := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
  have := mul_le_mul_of_nonneg_left h2 hx0
  nlinarith

/-- **`|ψ(x) − x| ≤ 1.82·10⁻⁹ x + 1145 √x + 4.2·10¹⁰`** for `x ≥ 10¹⁷`. -/
theorem psi_plateau {x : ℝ} (hx : 1e17 ≤ x) : |psiR x - x| ≤ 1.82e-9 * x + 1145 * √x + 4.2e10 := by
  have hx0 : 0 < x := by linarith
  set δ : ℝ := 7 / 3e10 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hKd : (7 : ℝ) * δ = 49 / 3e10 := by rw [hδ]; norm_num
  have hK2 : -((7 : ℝ) ^ 2 / 2) = -24.5 := by norm_num
  have he32 := exp_neg245_le
  have he32' : 0 < Real.exp (-24.5) := Real.exp_pos _
  have hsx := Real.sqrt_nonneg x
  -- upper
  have hK1 : 2 * Real.exp (-((7 : ℝ) ^ 2 / 2)) < 1 := by rw [hK2]; linarith
  have hYx : 1e10 * Real.exp (7 * δ) ≤ x := by
    rw [hKd]
    have := exp_small_le (t := (49 / 3e10 : ℝ)) (by norm_num) (by norm_num)
    nlinarith
  have hU := psi_upper_explicit (δ := δ) (K := 7) (y0 := 1e10) (x := x) hδ0 (by norm_num)
    hK1 (by norm_num) (by linarith) hYx
  rw [hK2, hKd] at hU
  have hEu := ErrG_plateau_le (a := 49 / 3e10) (by rw [abs_of_pos (by norm_num)]) hx
  rw [← hKd] at hEu
  rw [hKd] at hEu
  have hexp1 : Real.exp (δ ^ 2 / 2 + 49 / 3e10) ≤ 1 + 1.6334e-9 := by
    have h := exp_small_le2 (t := δ ^ 2 / 2 + 49 / 3e10) (by positivity) (by rw [hδ]; norm_num)
    rw [hδ] at h ⊢; norm_num at h ⊢; linarith
  have hexp2 : Real.exp (49 / 3e10) ≤ 1.0000001 := by
    have := exp_small_le (t := (49 / 3e10 : ℝ)) (by norm_num) (by norm_num); norm_num at this ⊢; linarith
  have hden : 1 / (1 - 2 * Real.exp (-24.5)) ≤ 1 + 4.7e-11 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hup : psiR x ≤ x + 1.82e-9 * x + 1145 * √x + 4.2e10 := by
    have hnum : Real.exp (δ ^ 2 / 2 + 49 / 3e10) * x + ErrG (49 / 3e10) (Real.log (1e10 / x)) δ x ≤
        (1 + 1.6334e-9) * x + (1143 * √x + 9.1e-11 * x + 1.09e7) := by
      have := mul_le_mul_of_nonneg_right hexp1 hx0.le; linarith
    have hnum0 : 0 ≤ (1 + 1.6334e-9) * x + (1143 * √x + 9.1e-11 * x + 1.09e7) := by positivity
    have hd0 : 0 < 1 - 2 * Real.exp (-24.5) := by linarith
    have hq : (Real.exp (δ ^ 2 / 2 + 49 / 3e10) * x + ErrG (49 / 3e10) (Real.log (1e10 / x)) δ x) /
        (1 - 2 * Real.exp (-24.5)) ≤ ((1 + 1.6334e-9) * x + (1143 * √x + 9.1e-11 * x + 1.09e7)) * (1 + 4.7e-11) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum hden (by positivity) hnum0
    have h4 : 4 * (1e10 * Real.exp (49 / 3e10)) ≤ 4.0001e10 := by nlinarith
    nlinarith
  -- lower
  have hb : Real.log (1e10 / x) ≤ -(7 * δ) := by
    rw [hKd]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1e10 / x by positivity)
    have : 1e10 / x ≤ 1e-7 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  have hL := psi_lower_explicit (δ := δ) (K := 7) (y0 := 1e10) (x := x) hδ0 (by rw [hδ]; norm_num)
    (by rw [hδ]; norm_num) (by norm_num) (by linarith) hb
  rw [hK2, hKd] at hL
  have hEl := ErrG_plateau_le (a := -(49 / 3e10)) (by rw [abs_neg, abs_of_pos (by norm_num)]) hx
  have hexp3 : 1 - 49 / 3e10 ≤ Real.exp (-(49 / 3e10)) := by
    have := Real.add_one_le_exp (-(49 / 3e10 : ℝ)); linarith
  have hlo : x - 1.82e-9 * x - 1145 * √x - 4.2e10 ≤ psiR x := by
    have := mul_le_mul_of_nonneg_right hexp3 hx0.le
    have : 4 * x * Real.exp (-24.5) ≤ 4 * x * 2.31e-11 := by
      have := mul_le_mul_of_nonneg_left he32 (by positivity : (0:ℝ) ≤ 4 * x); linarith
    nlinarith
  rw [abs_le]; constructor <;> linarith

end TernaryGoldbach.Explicit
