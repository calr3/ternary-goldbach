import TernaryGoldbach.Explicit.PsiExplicit
import TernaryGoldbach.Explicit.LogNumerics

/-!
# Constants for the Gaussian-smoothed explicit formula

Logarithms and window sums at the top of the range of heights (`H ≤ 3·10¹⁰`) that the height-generic
bounds allow, and the plateau parameters `δ = 7/H`, `K₀ = 7`, `y₀ = 10¹⁰` (used at `H = 10⁸` in
`PsiPlateau1e8.lean`).
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

theorem exp_small_le2 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ 1 + t + t ^ 2 := by
  have := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at this
  nlinarith [sq_nonneg t]

end TernaryGoldbach.Explicit
