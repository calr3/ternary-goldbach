/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Definitions for the formalization of `mobius003.tex`

Everything is indexed by natural numbers: `M`, `N`, `m`, `ρ`, `Q`, `Q₁` are step functions, so
the note's real-variable statements reduce to statements at integers. All sums run over
`Finset.Icc 1 x`, as in the statement files.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius


/-- `M(x) = ∑_{n ≤ x} μ(n)`. -/
noncomputable def M (x : ℕ) : ℝ := ∑ n ∈ Icc 1 x, (μ n : ℝ)

/-- `N(x) = ∑_{n ≤ x} μ(n) log n`. -/
noncomputable def N (x : ℕ) : ℝ := ∑ n ∈ Icc 1 x, (μ n : ℝ) * Real.log n

/-- `m(x) = ∑_{n ≤ x} μ(n)/n`. -/
noncomputable def msum (x : ℕ) : ℝ := ∑ n ∈ Icc 1 x, (μ n : ℝ) / n

/-- `ρ(x) = ∑_{k ≤ x} (Λ(k) − 1) = ψ(x) − x` (for natural `x`). -/
noncomputable def ρ (x : ℕ) : ℝ := ∑ k ∈ Icc 1 x, (Λ k - 1)

/-- `Q(x) = ∑_{n ≤ x} μ²(n)`. -/
noncomputable def Q (x : ℕ) : ℝ := ∑ n ∈ Icc 1 x, (μ n : ℝ) ^ 2

/-- `Q₁(x) = ∑_{n ≤ x} μ²(n)/n`. -/
noncomputable def Q1 (x : ℕ) : ℝ := ∑ n ∈ Icc 1 x, (μ n : ℝ) ^ 2 / n

/-- `κ = 6/π²`. -/
noncomputable def κ : ℝ := 6 / π ^ 2

/-- `S(x) = ∑_{1 ≤ t < x} |M(t)| log(1 + 1/t)`, the discrete form of `∫_1^x |M(t)| dt/t`. -/
noncomputable def S (x : ℕ) : ℝ := ∑ t ∈ Ico 1 x, |M t| * Real.log (1 + 1 / (t : ℝ))

/-- `I(a, b) = ∑_{a ≤ n < b} |N(n)| (1/log n − 1/log(n+1))`, the discrete form of
`∫_a^b |N(u)| du/(u log² u)`. -/
noncomputable def Iint (a b : ℕ) : ℝ :=
  ∑ n ∈ Ico a b, |N n| * (1 / Real.log n - 1 / Real.log (n + 1))

/-- `X₀ = 10⁹`. -/
def X0 : ℕ := 10 ^ 9

/-- `C₀ = M(X₀) − N(X₀)/log X₀`. -/
noncomputable def C0 : ℝ := M X0 - N X0 / Real.log X0

/-! ### Basic recurrences -/

theorem M_zero : M 0 = 0 := by simp [M]
theorem N_zero : N 0 = 0 := by simp [N]
theorem msum_zero : msum 0 = 0 := by simp [msum]
theorem ρ_zero : ρ 0 = 0 := by simp [ρ]
theorem Q_zero : Q 0 = 0 := by simp [Q]
theorem Q1_zero : Q1 0 = 0 := by simp [Q1]
theorem S_zero : S 0 = 0 := by simp [S]

theorem M_succ (x : ℕ) : M (x + 1) = M x + μ (x + 1) := by
  simp [M, sum_Icc_succ_top (by omega : 1 ≤ x + 1)]

theorem N_succ (x : ℕ) : N (x + 1) = N x + μ (x + 1) * Real.log (x + 1) := by
  simp [N, sum_Icc_succ_top (by omega : 1 ≤ x + 1)]

theorem msum_succ (x : ℕ) : msum (x + 1) = msum x + μ (x + 1) / (x + 1) := by
  simp [msum, sum_Icc_succ_top (by omega : 1 ≤ x + 1)]

theorem ρ_succ (x : ℕ) : ρ (x + 1) = ρ x + (Λ (x + 1) - 1) := by
  simp [ρ, sum_Icc_succ_top (by omega : 1 ≤ x + 1)]

theorem Q_succ (x : ℕ) : Q (x + 1) = Q x + (μ (x + 1) : ℝ) ^ 2 := by
  simp [Q, sum_Icc_succ_top (by omega : 1 ≤ x + 1)]

theorem Q1_succ (x : ℕ) : Q1 (x + 1) = Q1 x + (μ (x + 1) : ℝ) ^ 2 / (x + 1) := by
  simp [Q1, sum_Icc_succ_top (by omega : 1 ≤ x + 1)]

theorem S_succ {x : ℕ} (hx : 1 ≤ x) :
    S (x + 1) = S x + |M x| * Real.log (1 + 1 / (x : ℝ)) := by
  simp [S, sum_Ico_succ_top hx]

theorem moebius_sq_le_one (n : ℕ) : (μ n : ℝ) ^ 2 ≤ 1 := by
  have h := abs_moebius_le_one (n := n)
  have : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast h
  nlinarith [abs_nonneg (μ n : ℝ), sq_abs (μ n : ℝ)]

theorem abs_moebius_le_one' (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  exact_mod_cast abs_moebius_le_one (n := n)

theorem abs_M_le (x : ℕ) : |M x| ≤ x := by
  unfold M
  calc |∑ n ∈ Icc 1 x, (μ n : ℝ)| ≤ ∑ n ∈ Icc 1 x, |(μ n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 x, (1 : ℝ) := sum_le_sum fun n _ => abs_moebius_le_one' n
    _ = x := by simp

/-- `ρ(n) = ψ(n) − n` for natural `n`. -/
theorem ρ_eq_psi (n : ℕ) : ρ n = Chebyshev.psi n - n := by
  induction n with
  | zero => simp [ρ, Chebyshev.psi]
  | succ n ih =>
    rw [ρ_succ, ih]
    have h1 : Chebyshev.psi ((n + 1 : ℕ) : ℝ) = Chebyshev.psi (n : ℝ) + Λ (n + 1) := by
      simp only [Chebyshev.psi, Nat.floor_natCast]
      rw [sum_Ioc_succ_top (by omega)]
    rw [h1]; push_cast; ring

end TernaryGoldbach.RSBounds.Moebius003
