/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Inputs
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 4 of the note: bounds for `ρ`

`ρ(⌊v⌋) = (ψ(v) − v) + {v}`, so `|ρ(⌊v⌋)| ≤ |ψ(v) − v| + 1`; at natural `n`, `ρ(n) = ψ(n) − n`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Real

/-- `C₅ = 0.0077629`. -/
noncomputable def C5 : ℝ := 0.0077629

theorem exp22_le : Real.exp 22 ≤ 10 ^ 10 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 22 = Real.exp 1 ^ 22 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 22 ≤ (2.7182818286 : ℝ) ^ 22 := pow_le_pow_left₀ (Real.exp_pos 1).le h.le 22
    _ ≤ 10 ^ 10 := by norm_num

theorem rho_floor_eq (v : ℝ) : ρ ⌊v⌋₊ = (Chebyshev.psi v - v) + (v - ⌊v⌋₊) := by
  rw [ρ_eq_psi, ← Chebyshev.psi_eq_psi_coe_floor]; ring

theorem abs_rho_floor_le {v : ℝ} (hv : 0 ≤ v) : |ρ ⌊v⌋₊| ≤ |Chebyshev.psi v - v| + 1 := by
  rw [rho_floor_eq]
  have h1 := Nat.floor_le hv
  have h2 := Nat.lt_floor_add_one v
  calc |Chebyshev.psi v - v + (v - ⌊v⌋₊)| ≤ |Chebyshev.psi v - v| + |v - ⌊v⌋₊| := abs_add_le _ _
    _ ≤ |Chebyshev.psi v - v| + 1 := by
      gcongr; rw [abs_le]; constructor <;> linarith

/-- Lemma 4 with (P), real argument. -/
theorem rho_P (h : Inputs) {v : ℝ} (h1 : 1500 ≤ v) (h2 : v ≤ 10 ^ 10) :
    |ρ ⌊v⌋₊| ≤ 0.8 * Real.sqrt v + 1 := by
  have := h.P v h1 h2
  have := abs_rho_floor_le (v := v) (by linarith)
  norm_num at *; linarith

/-- Lemma 4 with (P), natural argument. -/
theorem rho_P_nat (h : Inputs) {n : ℕ} (h1 : 1500 ≤ n) (h2 : n ≤ 10 ^ 10) :
    |ρ n| ≤ 0.8 * Real.sqrt n := by
  have := h.P n (by exact_mod_cast h1) (by exact_mod_cast h2)
  rw [ρ_eq_psi]; norm_num at *; linarith

/-- Lemma 4 with (S), real argument. -/
theorem rho_S (h : Inputs) {v : ℝ} (h1 : Real.exp 22 ≤ v) :
    |ρ ⌊v⌋₊| ≤ C5 * v / Real.log v + 1 := by
  have := h.S v h1
  have := abs_rho_floor_le (v := v) (le_trans (Real.exp_pos 22).le h1)
  simp only [C5]; linarith

/-- Lemma 4 with (S), natural argument. -/
theorem rho_S_nat (h : Inputs) {n : ℕ} (h1 : Real.exp 22 ≤ n) :
    |ρ n| ≤ C5 * n / Real.log n := by
  have := h.S n h1
  rw [ρ_eq_psi]; simp only [C5]; linarith

end TernaryGoldbach.RSBounds.Moebius003
