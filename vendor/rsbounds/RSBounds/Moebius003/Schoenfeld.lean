/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Abel

/-!
# Lemma 1 of the note: Schoenfeld's identity

For natural numbers `1 ≤ y ≤ x`,
`N(x) + 1 = M(x) − ∑_{2 ≤ k ≤ y} (Λ(k) − 1) M(x/k) − ∑_{j ≤ x/y} μ(j) ρ(x/j) + ρ(y) M(x/y)`,
with floor (natural) division throughout.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- `μ log = −Λ ⋆ μ`. -/
theorem vonMangoldt_mul_moebius_apply (n : ℕ) :
    ((Λ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) n = -((μ n : ℝ) * Real.log n) := by
  have h1 : (pmul (μ : ArithmeticFunction ℝ) log) * (ζ : ArithmeticFunction ℝ) = -Λ := by
    ext k
    rw [coe_mul_zeta_apply]
    simp only [pmul_apply, intCoe_apply, log_apply, ArithmeticFunction.neg_apply]
    exact sum_moebius_mul_log_eq
  have h2 : pmul (μ : ArithmeticFunction ℝ) log = -(Λ * (μ : ArithmeticFunction ℝ)) := by
    have := congrArg (· * (μ : ArithmeticFunction ℝ)) h1
    simpa only [mul_assoc, coe_zeta_mul_coe_moebius, mul_one, neg_mul] using this
  have := congrArg (fun f : ArithmeticFunction ℝ => f n) h2
  simp only [pmul_apply, intCoe_apply, log_apply, ArithmeticFunction.neg_apply] at this
  linarith

/-- `∑_{k ≤ x} M(x/k) = 1` for `x ≥ 1`. -/
theorem sum_M_div (x : ℕ) (hx : 1 ≤ x) : ∑ k ∈ Icc 1 x, M (x / k) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum (ζ : ArithmeticFunction ℝ) (μ : ArithmeticFunction ℝ) x
  rw [coe_zeta_mul_coe_moebius] at h
  have hl : ∑ n ∈ Ioc 0 x, (1 : ArithmeticFunction ℝ) n = 1 := by
    rw [sum_eq_single 1]
    · simp
    · intro b _ hb; simp [one_apply_ne hb]
    · intro h1; simp at h1; omega
  rw [hl] at h
  rw [Icc_one_eq_Ioc_zero, h]
  refine sum_congr rfl fun k hk => ?_
  simp only [mem_Ioc] at hk
  rw [natCoe_apply, zeta_apply, ite_eq_right_iff.mpr (fun h => absurd h (by omega)), M, Icc_one_eq_Ioc_zero]
  simp

/-- `N(x) = −∑_{k ≤ x} Λ(k) M(x/k)`. -/
theorem N_eq_neg_sum (x : ℕ) : N x = -∑ k ∈ Icc 1 x, Λ k * M (x / k) := by
  have h := sum_Ioc_mul_eq_sum_sum (Λ : ArithmeticFunction ℝ) (μ : ArithmeticFunction ℝ) x
  simp only [vonMangoldt_mul_moebius_apply, sum_neg_distrib] at h
  simp only [N, Icc_one_eq_Ioc_zero]
  have : ∑ n ∈ Ioc 0 x, (μ n : ℝ) * Real.log n = -∑ n ∈ Ioc 0 x, Λ n * ∑ m ∈ Ioc 0 (x / n), ((μ : ArithmeticFunction ℝ) m) := by
    linarith
  rw [this]
  congr 1

/-- `N(x) + 1 = −∑_{k ≤ x} (Λ(k) − 1) M(x/k)` for `x ≥ 1`. -/
theorem N_add_one_eq (x : ℕ) (hx : 1 ≤ x) :
    N x + 1 = -∑ k ∈ Icc 1 x, (Λ k - 1) * M (x / k) := by
  have h1 := sum_M_div x hx
  rw [N_eq_neg_sum]
  simp only [sub_mul, one_mul, sum_sub_distrib]
  linarith

/-- The pairs `(k, m)` with `k > y` and `km ≤ x`. -/
theorem sum_Ioc_swap (x y : ℕ) (hy : 1 ≤ y) (f g : ℕ → ℝ) :
    ∑ k ∈ Ioc y x, f k * ∑ m ∈ Icc 1 (x / k), g m =
      ∑ m ∈ Icc 1 (x / y), g m * ∑ k ∈ Ioc y (x / m), f k := by
  simp only [mul_sum]
  rw [sum_comm' (t' := Icc 1 (x / y)) (s' := fun m => Ioc y (x / m))]
  · exact sum_congr rfl fun m _ => sum_congr rfl fun k _ => by ring
  · intro k m
    simp only [mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hm1, hm2⟩
      have hkpos : 0 < k := by omega
      have h1 : m * k ≤ x := (Nat.le_div_iff_mul_le hkpos).1 hm2
      refine ⟨⟨hk1, ?_⟩, hm1, ?_⟩
      · exact (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
      · exact (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
    · rintro ⟨⟨hk1, hk2⟩, hm1, hm2⟩
      have h1 : k * m ≤ x := (Nat.le_div_iff_mul_le (by omega)).1 hk2
      refine ⟨⟨hk1, ?_⟩, hm1, ?_⟩
      · nlinarith
      · exact (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)

/-- **Lemma 1** (Schoenfeld 1969, (19)), at natural `x` and `y`. -/
theorem schoenfeld_identity {x y : ℕ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    N x + 1 = M x - ∑ k ∈ Icc 2 y, (Λ k - 1) * M (x / k)
      - ∑ j ∈ Icc 1 (x / y), (μ j : ℝ) * ρ (x / j) + ρ y * M (x / y) := by
  rw [N_add_one_eq x (by omega)]
  -- split `Icc 1 x` into `Icc 1 y` and `Ioc y x`
  have hsplit : ∑ k ∈ Icc 1 x, (Λ k - 1) * M (x / k) =
      ∑ k ∈ Icc 1 y, (Λ k - 1) * M (x / k) + ∑ k ∈ Ioc y x, (Λ k - 1) * M (x / k) := by
    rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero, sum_Ioc_consecutive _ (by omega) hyx]
  have hone : ∑ k ∈ Icc 1 y, (Λ k - 1) * M (x / k) =
      -M x + ∑ k ∈ Icc 2 y, (Λ k - 1) * M (x / k) := by
    rw [← insert_Icc_add_one_left_eq_Icc (by omega : 1 ≤ y), sum_insert (by simp)]
    simp [M]
  have hswap : ∑ k ∈ Ioc y x, (Λ k - 1) * M (x / k) =
      ∑ j ∈ Icc 1 (x / y), (μ j : ℝ) * (ρ (x / j) - ρ y) := by
    have := sum_Ioc_swap x y hy (fun k => Λ k - 1) (fun m => (μ m : ℝ))
    rw [show (∑ k ∈ Ioc y x, (Λ k - 1) * M (x / k)) =
      ∑ k ∈ Ioc y x, (Λ k - 1) * ∑ m ∈ Icc 1 (x / k), (μ m : ℝ) from rfl, this]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_Icc] at hj
    congr 1
    have hyj : y ≤ x / j := (Nat.le_div_iff_mul_le (by omega)).2
      (by have := (Nat.le_div_iff_mul_le (by omega)).1 hj.2; linarith [mul_comm j y])
    have hc := sum_Ioc_consecutive (fun k => Λ k - 1) (Nat.zero_le y) hyj
    simp only [ρ, Icc_one_eq_Ioc_zero]
    linarith
  rw [hsplit, hone, hswap]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul]
  rw [show ∑ j ∈ Icc 1 (x / y), (μ j : ℝ) = M (x / y) from rfl]
  ring

end TernaryGoldbach.RSBounds.Moebius003
