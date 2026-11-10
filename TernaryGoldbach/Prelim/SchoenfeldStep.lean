import TernaryGoldbach.Prelim.ElMarraki
import TernaryGoldbach.Prelim.SqfreeQ1
import TernaryGoldbach.Prelim.WeightsWalk

/-!
# One step of Schoenfeld's induction

`N_abs_le`: from Schoenfeld's identity, for `1 ≤ Y ≤ D`,
`|N(D)| ≤ |M(D)| + 1 + ∑_{1 < k ≤ Y} a_k |M(D/k)| + ∑_{m ≤ D/(Y+1)} μ²(m) |ρ(D/m)| + |ρ(Y)| |M(D/(Y+1))|`,
`a_k = |Λ(k) − 1|`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sch
open TernaryGoldbach.Prelim.Wts (aw)
open TernaryGoldbach.Prelim.Sqf (sq)

theorem abs_mu_eq_sq (m : ℕ) : |(μ m : ℝ)| = sq m := by
  unfold sq
  by_cases h : Squarefree m
  · rw [if_pos h, ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast; rw [abs_pow, abs_neg, abs_one, one_pow]
  · rw [if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; simp

theorem N_abs_le {D Y : ℕ} (hY1 : 1 ≤ Y) (hYD : Y ≤ D) :
    |Nn D| ≤ |Mn D| + 1 + ∑ k ∈ Ioc 1 Y, aw k * |Mn (D / k)| +
      ∑ m ∈ Ioc 0 (D / (Y + 1)), sq m * |ρn (D / m)| + |ρn Y| * |Mn (D / (Y + 1))| := by
  have h := schoenfeld_identity hY1 hYD
  have e : Nn D = Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k) -
      ∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m) + ρn Y * Mn (D / (Y + 1)) - 1 := by linarith
  rw [e]
  have h1 : |∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k)| ≤
      ∑ k ∈ Ioc 1 Y, aw k * |Mn (D / k)| :=
    (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun k _ => by rw [abs_mul]; rfl))
  have h2 : |∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m)| ≤
      ∑ m ∈ Ioc 0 (D / (Y + 1)), sq m * |ρn (D / m)| :=
    (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun m _ => by rw [abs_mul, abs_mu_eq_sq]))
  have h3 : |ρn Y * Mn (D / (Y + 1))| = |ρn Y| * |Mn (D / (Y + 1))| := abs_mul _ _
  calc |Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k) -
        ∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m) + ρn Y * Mn (D / (Y + 1)) - 1|
      ≤ |Mn D| + |∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k)| +
        |∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m)| + |ρn Y * Mn (D / (Y + 1))| + 1 := by
        have := abs_sub (Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k) -
          ∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m) + ρn Y * Mn (D / (Y + 1))) 1
        have := abs_add_le (Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k) -
          ∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m)) (ρn Y * Mn (D / (Y + 1)))
        have := abs_sub (Mn D - ∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k))
          (∑ m ∈ Ioc 0 (D / (Y + 1)), (μ m : ℝ) * ρn (D / m))
        have := abs_sub (Mn D) (∑ k ∈ Ioc 1 Y, (ArithmeticFunction.vonMangoldt k - 1) * Mn (D / k))
        simp only [abs_one] at *
        linarith
    _ ≤ _ := by rw [h3]; linarith

end TernaryGoldbach.Prelim.Sch
