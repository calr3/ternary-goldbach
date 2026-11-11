/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Defs

/-!
# Summation by parts on `Icc 1 K`
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Finset

/-- Abel summation: `∑_{k ≤ K} f(k) g(k) = F(K) g(K) − ∑_{1 ≤ i < K} F(i) (g(i+1) − g(i))`,
with `F(i) = ∑_{k ≤ i} f(k)`. -/
theorem sum_mul_eq_abel (f g : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Icc 1 K, f k * g k =
      (∑ k ∈ Icc 1 K, f k) * g K - ∑ i ∈ Ico 1 K, (∑ k ∈ Icc 1 i, f k) * (g (i + 1) - g i) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · rw [sum_Ico_succ_top hK]
      ring

/-- Abel summation in "telescoped" form: `∑_{k ≤ K} f(k) (g(K+1) − g(k)) = ∑_{i ≤ K} F(i) (g(i+1) − g(i))`. -/
theorem sum_mul_sub_eq (f g : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Icc 1 K, f k * (g (K + 1) - g k) =
      ∑ i ∈ Icc 1 K, (∑ k ∈ Icc 1 i, f k) * (g (i + 1) - g i) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ← ih, sum_Icc_succ_top (by omega)]
    have : ∑ k ∈ Icc 1 K, f k * (g (K + 1 + 1) - g k) =
        ∑ k ∈ Icc 1 K, f k * (g (K + 1) - g k) + (∑ k ∈ Icc 1 K, f k) * (g (K + 1 + 1) - g (K + 1)) := by
      rw [sum_mul, ← sum_add_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [this]; ring

/-- Telescoping on `Icc 1 K`. -/
theorem sum_Icc_sub_telescope (g : ℕ → ℝ) (K : ℕ) :
    ∑ i ∈ Icc 1 K, (g (i + 1) - g i) = g (K + 1) - g 1 := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_Icc_succ_top (by omega), ih]; ring

/-- Telescoping on `Ico a b`. -/
theorem sum_Ico_sub_telescope (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Ico a b, (g (i + 1) - g i) = g b - g a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [sum_Ico_succ_top hab, ih]; ring

theorem Icc_one_eq_Ioc_zero (x : ℕ) : Icc 1 x = Ioc 0 x := by
  ext n; simp only [mem_Icc, mem_Ioc]; omega

/-- Abel comparison: if the partial sums of `f` are dominated by those of `f'`, and `g ≥ 0` is
non-increasing on `[1, K]`, then `∑ f g ≤ ∑ f' g`. -/
theorem abel_compare (f f' g : ℕ → ℝ) (K : ℕ)
    (hF : ∀ i, 1 ≤ i → i ≤ K → ∑ k ∈ Icc 1 i, f k ≤ ∑ k ∈ Icc 1 i, f' k)
    (hg : ∀ i, 1 ≤ i → i < K → g (i + 1) ≤ g i) (hgK : 0 ≤ g K) :
    ∑ k ∈ Icc 1 K, f k * g k ≤ ∑ k ∈ Icc 1 K, f' k * g k := by
  rw [sum_mul_eq_abel f g K, sum_mul_eq_abel f' g K]
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have h1 : (∑ k ∈ Icc 1 K, f k) * g K ≤ (∑ k ∈ Icc 1 K, f' k) * g K :=
    mul_le_mul_of_nonneg_right (hF K hK le_rfl) hgK
  have h2 : ∑ i ∈ Ico 1 K, (∑ k ∈ Icc 1 i, f' k) * (g (i + 1) - g i) ≤
      ∑ i ∈ Ico 1 K, (∑ k ∈ Icc 1 i, f k) * (g (i + 1) - g i) := by
    refine sum_le_sum fun i hi => ?_
    obtain ⟨hi1, hi2⟩ := mem_Ico.1 hi
    have := hF i hi1 hi2.le
    have := hg i hi1 hi2
    nlinarith
  linarith

end TernaryGoldbach.RSBounds.Moebius003
