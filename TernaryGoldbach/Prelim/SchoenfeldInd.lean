import TernaryGoldbach.Prelim.Schoenfeld69

/-!
# `M` from `N`, discretely

`M_of_N`: for `1 ≤ a < b`,
`M(b) = C(a) + N(b)/log b + ∑_{a < n < b} N(n) (1/log n − 1/log(n+1))`, where
`C(a) = M(a) − N(a)/log(a+1) = (∑_{n ≤ a} M(n) log(1 + 1/n))/log(a+1)` (`C_eq`).
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim.Sch

theorem Mn_succ (k : ℕ) : Mn (k + 1) = Mn k + μ (k + 1) := by
  unfold Mn; rw [Finset.sum_Ioc_succ_top (by omega)]

theorem Nn_succ (k : ℕ) : Nn (k + 1) = Nn k + μ (k + 1) * Real.log (k + 1 : ℕ) := by
  unfold Nn; rw [Finset.sum_Ioc_succ_top (by omega)]

theorem log_succ_pos (a : ℕ) (ha : 1 ≤ a) : 0 < Real.log ((a : ℝ) + 1) :=
  Real.log_pos (by have : (1 : ℝ) ≤ a := by exact_mod_cast ha
                   linarith)

/-- **`M` from `N`** (summation by parts with weight `1/log`). -/
theorem M_of_N {a : ℕ} (ha : 1 ≤ a) : ∀ b, a < b →
    Mn b = (Mn a - Nn a / Real.log ((a : ℝ) + 1)) + Nn b / Real.log b +
      ∑ n ∈ Ioo a b, Nn n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
    rw [Mn_succ, Nn_succ, show Ioo a (a + 1) = ∅ by ext x; simp, sum_empty]
    have hl := log_succ_pos a ha
    push_cast
    field_simp
    ring
  | succ b hb ih =>
    have hb1 : 2 ≤ b := by omega
    have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb1)
    have hlb1 : 0 < Real.log ((b : ℝ) + 1) := log_succ_pos b (by omega)
    rw [Mn_succ, ih, Nn_succ, show Ioo a (b + 1) = insert b (Ioo a b) by ext x; simp; omega,
      sum_insert (by simp)]
    push_cast
    field_simp
    ring

/-- `M(a) − N(a)/log(a+1) = (∑_{n ≤ a} M(n) log((n+1)/n)) / log(a+1)`. -/
theorem C_eq : ∀ a, 1 ≤ a → Mn a - Nn a / Real.log ((a : ℝ) + 1) =
    (∑ n ∈ Ioc 0 a, Mn n * (Real.log ((n : ℝ) + 1) - Real.log n)) / Real.log ((a : ℝ) + 1) := by
  intro a ha
  have key : ∀ a, Mn a * Real.log ((a : ℝ) + 1) - Nn a =
      ∑ n ∈ Ioc 0 a, Mn n * (Real.log ((n : ℝ) + 1) - Real.log n) := by
    intro a
    induction a with
    | zero => simp [Mn, Nn]
    | succ a ih =>
      rw [Finset.sum_Ioc_succ_top (by omega), ← ih, Mn_succ, Nn_succ]
      push_cast
      ring
  have hl := log_succ_pos a ha
  rw [← key a]
  field_simp

end TernaryGoldbach.Prelim.Sch
