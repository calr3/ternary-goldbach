import Mathlib

/-!
# Vaughan's identity

For `U, V ≥ 0`, writing `f_{≤U}` for `f` truncated to `n ≤ U` and `f_{>U} = f - f_{≤U}`,

`Λ = Λ_{≤V} + μ_{≤U} * log - μ_{≤U} * Λ_{≤V} * 1 + μ_{>U} * Λ_{>V} * 1`

as Dirichlet convolutions.  In particular, for `n > V`,
`Λ(n) = (μ_{≤U} * log)(n) - (μ_{≤U} * Λ_{≤V} * 1)(n) + (μ_{>U} * Λ_{>V} * 1)(n)`.

This is [H, (3.6)], the starting point of the minor-arc estimates of [H, Part I].  [H, (3.6)]
prints `+ μ_{≤U} * Λ_{≤V} * 1`; the derivation that follows it, and (3.8), have `-`.

Proved, with no `sorry`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TernaryGoldbach.MinorArcs

/-- The truncation `f_{≤U}(n) = f(n) [n ≤ U]`. -/
def trunc (f : ArithmeticFunction ℝ) (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

theorem sub_apply' (f g : ArithmeticFunction ℝ) (n : ℕ) : (f - g) n = f n - g n := rfl

@[simp] theorem trunc_apply (f : ArithmeticFunction ℝ) (U n : ℕ) :
    trunc f U n = if n ≤ U then f n else 0 := rfl

/-- **Vaughan's identity**, as an identity of arithmetic functions. -/
theorem vaughan (U V : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      trunc Λ V + trunc μ U * log - trunc μ U * trunc Λ V * ζ +
        ((μ : ArithmeticFunction ℝ) - trunc μ U) * (Λ - trunc Λ V) * ζ := by
  have h1 : (μ : ArithmeticFunction ℝ) * ζ = 1 := coe_moebius_mul_coe_zeta
  have h2 : (Λ : ArithmeticFunction ℝ) * ζ = log := vonMangoldt_mul_zeta
  linear_combination (-(Λ : ArithmeticFunction ℝ) + trunc Λ V) * h1 + trunc μ U * h2

/-- **Vaughan's identity**, pointwise for `n > V`. -/
theorem vaughan_apply {U V n : ℕ} (hn : V < n) :
    Λ n = (trunc μ U * log) n - (trunc μ U * trunc Λ V * ζ) n +
      (((μ : ArithmeticFunction ℝ) - trunc μ U) * (Λ - trunc Λ V) * ζ) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan U V)
  simp only [ArithmeticFunction.add_apply, sub_apply', trunc_apply, ite_eq_right (not_le.2 hn), zero_add] at h
  exact h

end TernaryGoldbach.MinorArcs
