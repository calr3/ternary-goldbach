/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Abel

/-!
# Lemma 2 of the note: `M` in terms of `N`

Discrete form: for `2 ≤ X ≤ x`,
`M(x) = (M(X) − N(X)/log X) + N(x)/log x + ∑_{X ≤ n < x} N(n) (1/log n − 1/log(n+1))`.
The sum is exactly `∫_X^x N(u) du/(u log² u)`, since `N` is constant on `[n, n+1)`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius

theorem log_nat_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log n :=
  Real.log_pos (by exact_mod_cast (by omega : 1 < n))

/-- **Lemma 2**, first identity. -/
theorem M_eq_of_N {X x : ℕ} (hX : 2 ≤ X) (hx : X ≤ x) :
    M x = (M X - N X / Real.log X) + N x / Real.log x +
      ∑ n ∈ Ico X x, N n * (1 / Real.log n - 1 / Real.log (n + 1)) := by
  induction x, hx using Nat.le_induction with
  | base => simp
  | succ x hx ih =>
    rw [sum_Ico_succ_top hx, M_succ, N_succ, ih]
    have h1 : 0 < Real.log ((x : ℝ) + 1) := by
      have := log_nat_pos (n := x + 1) (by omega); push_cast at this; exact this
    have h2 : 0 < Real.log (x : ℝ) := log_nat_pos (by omega)
    push_cast
    field_simp
    ring

/-- `M(x) log x − N(x) = ∑_{1 ≤ n < x} M(n) (log(n+1) − log n)`. -/
theorem M_mul_log_sub_N (x : ℕ) :
    M x * Real.log x - N x = ∑ n ∈ Ico 1 x, M n * (Real.log (n + 1) - Real.log n) := by
  induction x with
  | zero => simp [M, N]
  | succ x ih =>
    rw [M_succ, N_succ]
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [M, N]
    · rw [sum_Ico_succ_top hx, ← ih]; push_cast; ring

/-- **Lemma 2**, second identity: `M(X) − N(X)/log X = (1/log X) ∑_{n < X} M(n) log((n+1)/n)`. -/
theorem M_sub_N_div_log {X : ℕ} (hX : 2 ≤ X) :
    M X - N X / Real.log X =
      (∑ n ∈ Ico 1 X, M n * (Real.log (n + 1) - Real.log n)) / Real.log X := by
  rw [← M_mul_log_sub_N]
  have := log_nat_pos hX
  field_simp

theorem log_succ_sub_log {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n = Real.log (1 + 1 / (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn'.ne']
  congr 1; field_simp

theorem abs_M_sub_N_div_log_le {X : ℕ} (hX : 2 ≤ X) :
    |M X - N X / Real.log X| ≤ S X / Real.log X := by
  rw [M_sub_N_div_log hX, abs_div, abs_of_pos (log_nat_pos hX)]
  gcongr
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Ico.1 hn).1
  have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  rw [abs_mul, log_succ_sub_log hn1, abs_of_nonneg (Real.log_nonneg (by linarith))]

theorem abs_C0_le : |C0| ≤ S X0 / Real.log X0 :=
  abs_M_sub_N_div_log_le (by norm_num [X0])

/-- `0 ≤ 1/log n − 1/log(n+1)` for `n ≥ 2`. -/
theorem inv_log_sub_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ 1 / Real.log n - 1 / Real.log (n + 1) := by
  have h1 := log_nat_pos hn
  have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le h1 h2

/-- `n (1/log n − 1/log(n+1)) ≤ 1/log² n` for `n ≥ 2`. -/
theorem mul_inv_log_sub_le {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * (1 / Real.log n - 1 / Real.log (n + 1)) ≤ 1 / Real.log n ^ 2 := by
  have h1 := log_nat_pos hn
  have hn' : (0 : ℝ) < n := by positivity
  have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have h3 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [log_succ_sub_log (by omega)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (n : ℝ) by positivity)
    linarith
  have h4 : 0 < Real.log ((n : ℝ) + 1) := by linarith
  rw [div_sub_div _ _ h1.ne' h4.ne', one_mul, mul_one, mul_div_assoc']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (n : ℝ) * (Real.log (↑n + 1) - Real.log ↑n) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h3 hn'.le
    rwa [mul_one_div_cancel hn'.ne'] at this
  nlinarith [mul_le_mul_of_nonneg_left h2 h1.le]

/-- The bound for `|M|` from Lemma 2: `|M(x)| ≤ |C₀| + |N(x)|/log x + I(X₀, x)` for `x ≥ X₀`. -/
theorem abs_M_le_of_N {x : ℕ} (hx : X0 ≤ x) :
    |M x| ≤ |C0| + |N x| / Real.log x + Iint X0 x := by
  have hX : 2 ≤ X0 := by norm_num [X0]
  rw [M_eq_of_N hX hx]
  have hlog : 0 < Real.log x := log_nat_pos (by omega)
  calc |C0 + N x / Real.log x + ∑ n ∈ Ico X0 x, N n * (1 / Real.log n - 1 / Real.log (n + 1))|
      ≤ |C0| + |N x / Real.log x| +
          |∑ n ∈ Ico X0 x, N n * (1 / Real.log n - 1 / Real.log (n + 1))| := abs_add_three _ _ _
    _ ≤ |C0| + |N x| / Real.log x + Iint X0 x := by
      rw [abs_div, abs_of_pos hlog]
      gcongr
      refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine sum_congr rfl fun n hn => ?_
      rw [abs_mul, abs_of_nonneg (inv_log_sub_nonneg (by have := (mem_Ico.1 hn).1; omega))]

theorem Iint_add {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Iint a c = Iint a b + Iint b c := by
  unfold Iint; rw [sum_Ico_consecutive _ hab hbc]

/-- On a range where `|N(n)| ≤ ν n`, `I(a, b) ≤ ν (b − a)/log² a`. -/
theorem Iint_le {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) {ν La : ℝ} (hν : 0 ≤ ν)
    (hLa : 0 < La) (hLa' : La ≤ Real.log a)
    (hN : ∀ n, a ≤ n → n < b → |N n| ≤ ν * n) :
    Iint a b ≤ ν * ((b : ℝ) - a) / La ^ 2 := by
  unfold Iint
  have hcard : ((b : ℝ) - a) = ∑ n ∈ Ico a b, (1 : ℝ) := by
    simp [Nat.cast_sub hab]
  rw [hcard, mul_sum, sum_div]
  refine sum_le_sum fun n hn => ?_
  obtain ⟨h1, h2⟩ := mem_Ico.1 hn
  have hn2 : 2 ≤ n := by omega
  have hd := inv_log_sub_nonneg hn2
  have hlog : La ≤ Real.log n :=
    hLa'.trans (Real.log_le_log (by positivity) (by exact_mod_cast h1))
  calc |N n| * (1 / Real.log n - 1 / Real.log (n + 1))
      ≤ ν * n * (1 / Real.log n - 1 / Real.log (n + 1)) := by gcongr; exact hN n h1 h2
    _ = ν * (n * (1 / Real.log n - 1 / Real.log (n + 1))) := by ring
    _ ≤ ν * (1 / Real.log n ^ 2) := by gcongr; exact mul_inv_log_sub_le hn2
    _ ≤ ν * (1 / La ^ 2) := by gcongr
    _ = ν * 1 / La ^ 2 := by ring

end TernaryGoldbach.RSBounds.Moebius003
