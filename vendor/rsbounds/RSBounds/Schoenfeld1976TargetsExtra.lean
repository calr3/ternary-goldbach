import RSBounds.Schoenfeld1976Targets

/-!
# The other displays of Schoenfeld (1976), Theorem 7*

`Schoenfeld1976Targets` states (5.6*) and (5.6b*). This file states the other three displays of
Theorem 7*, (5.5a*), (5.5b*) and (5.6a*), as transcribed in `docs/Schoenfeld1976Plan.md`
(lines 38–40). They are specifications, not proofs or axioms, and keep the finite RH verification
as an explicit premise, like the other targets.

It also states `PsiCert`, a finite computation certified outside this project, which the proofs
of these displays (and of (5.6*) on `[1.35·10⁶, e^22]`) take as a hypothesis.
-/

namespace TernaryGoldbach.RSBounds.Goals.Schoenfeld1976

/-- PsiCert: `|ψ(x) − x| ≤ (4/5)√x` for `1500 ≤ x ≤ 10¹⁰`. -/
def PsiCert : Prop :=
  ∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x

/-- Theorem 7*, equation (5.5a*). -/
def PsiLog : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, 161971 ≤ x →
    |Chebyshev.psi x - x| < 0.0220646 * x / Real.log x

/-- Theorem 7*, equation (5.5b*). -/
def PsiLogLower : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, 89909 ≤ x →
    -(0.0220646 * x / Real.log x) < Chebyshev.psi x - x

/-- Theorem 7*, equation (5.6a*). -/
def ThetaLogUpper : Prop :=
  FiniteRH 1894438.5122 → ∀ x : ℝ, 1 < x →
    Chebyshev.theta x - x < 0.0201384 * x / Real.log x

end TernaryGoldbach.RSBounds.Goals.Schoenfeld1976
