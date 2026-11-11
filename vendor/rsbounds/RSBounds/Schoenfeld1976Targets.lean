import RSBounds.Targets

/-!
# Exact targets from Schoenfeld, Sharper bounds II (1976)

These are specifications, not proofs or axioms. They retain the finite RH
verification through 1894438.5122 as an explicit premise. The constants, strict
inequalities and closed lower endpoints were checked against the supplied scan,
printed pages 342 (Theorem 11) and 357 (Theorem 7*), and rechecked against the
scan on 2026-11-07.

Theorem 11's analytic proof starts at exp 1737; its smaller ranges require the
paper's separate table and finite checks. The targets below include those ranges.

Theorem 11 is targeted in full: (7.2), (7.3) and (7.4). The printed (7.4),
"θ(x) - x ≤ ψ(x) - x ε₀(x) if 1 ≤ x", has lost a relation; `PsiUpperTheorem11`
states the form that the proof on printed page 349 establishes.

This file targets (5.6*) and (5.6b*) of Theorem 7*. Its other displays,
(5.5a*), (5.5b*) and (5.6a*), are in `Schoenfeld1976TargetsExtra`.
-/

namespace TernaryGoldbach.RSBounds.Goals.Schoenfeld1976

noncomputable def X (x : ℝ) : ℝ := Real.sqrt (Real.log x / 9.645908801)

noncomputable def epsilon0 (x : ℝ) : ℝ :=
  Real.sqrt (8 / (17 * Real.pi)) * Real.sqrt (X x) * Real.exp (-X x)

/-- Theorem 11, equation (7.2), including the smaller-range extensions. -/
def PsiTheorem11 : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, 17 ≤ x →
    |Chebyshev.psi x - x| < x * epsilon0 x

/-- Theorem 11, equation (7.3), including the smaller-range extensions. -/
def ThetaTheorem11 : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, 101 ≤ x →
    |Chebyshev.theta x - x| < x * epsilon0 x

/-- Theorem 11, equation (7.4), in the form established on printed page 349:
the printed display omits the relation before `x * ε₀(x)`. -/
def PsiUpperTheorem11 : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, 1 ≤ x →
    Chebyshev.theta x - x ≤ Chebyshev.psi x - x ∧
      Chebyshev.psi x - x < x * epsilon0 x

/-- Theorem 7*, equation (5.6*). -/
def ThetaLog : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, 758711 ≤ x →
    |Chebyshev.theta x - x| < 0.0239922 * x / Real.log x

/-- Theorem 7*, equation (5.6b*); the statement includes both functions. -/
def PsiThetaLog : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, Real.exp 22 ≤ x →
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
    |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x

end TernaryGoldbach.RSBounds.Goals.Schoenfeld1976
