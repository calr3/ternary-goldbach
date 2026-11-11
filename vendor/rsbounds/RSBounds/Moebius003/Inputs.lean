/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003Statement
import RSBounds.Moebius003.Defs

/-!
# The inputs of the note, bundled

`Inputs` collects the hypotheses of `Target` in the form the proof uses: the `ψ` half of (S)
(already under finite RH), (P), (M), (m) and (L).
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Real

/-- The inputs (S), (P), (M), (m), (L) of the note. -/
structure Inputs : Prop where
  /-- (S): Schoenfeld's (5.6b*), `ψ` half, for `x ≥ e²²`. -/
  S : ∀ x : ℝ, Real.exp 22 ≤ x → |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x
  /-- (P): PsiCert. -/
  P : Goals.Schoenfeld1976.PsiCert
  /-- (M): `|M(n)| ≤ 0.571 √n` for `33 ≤ n ≤ 10⁹`. -/
  Mert : MoebiusInputs.MertensSqrt
  /-- (m): `|m(n)| log(n + 1) ≤ 0.03` for `11815 ≤ n ≤ 6·10⁵`. -/
  small : MoebiusInputs.SmallMoebiusSum
  /-- (L), first half: `A(n) ≤ 2(n − 1)` for `1 ≤ n ≤ 2²⁰`. -/
  W : LambdaInputs.WeightSumBound
  /-- (L), second half: the enclosures of `G` and `H` at the 45 checkpoints. -/
  GH : LambdaInputs.GHBounds

theorem Inputs.of_target_hyps (hS : Goals.Schoenfeld1976.PsiThetaLog)
    (hP : Goals.Schoenfeld1976.PsiCert) (hM : MoebiusInputs.MertensSqrt)
    (hm : MoebiusInputs.SmallMoebiusSum) (hW : LambdaInputs.WeightSumBound)
    (hGH : LambdaInputs.GHBounds) (hRH : Goals.FiniteRH 1894438.5122) : Inputs :=
  ⟨fun x hx => (hS hRH x hx).1, hP, hM, hm, hW, hGH⟩

end TernaryGoldbach.RSBounds.Moebius003
