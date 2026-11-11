/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Schoenfeld1976TargetsExtra
import RSBounds.MoebiusInputs
import RSBounds.LambdaInputs

/-!
# Target of the formalization of `mobius003.tex`

The note proves `|∑_{n ≤ x} μ(n)/n| ≤ 0.03 / log x` for every real `x ≥ 11815` from:
* (S) Schoenfeld's (5.6b*), `Goals.Schoenfeld1976.PsiThetaLog` (under finite RH to
  `1894438.5122`; only its `ψ` half is needed, and only for `x > 10¹⁰`);
* (P) PsiCert, `Goals.Schoenfeld1976.PsiCert`;
* (M) and (m), `MoebiusInputs`;
* (L), `LambdaInputs`;
* (q) `μ²(n)` for `n ≤ 10⁴`, a small computation that the proof itself carries out.

`RamareMoebius` is upstream's hypothesis of the same name (`calr3/ternary-goldbach`,
`TernaryGoldbach/Statement.lean` at `192ca57`), verbatim. Statements only; the closure is Mathlib.
-/

namespace TernaryGoldbach.RSBounds.Moebius003
open Goals

/-- Upstream's `RamareMoebius`, verbatim. -/
def RamareMoebius : Prop :=
  ∀ x : ℝ, 11815 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n| ≤ 0.03 / Real.log x

/-- The note's theorem, from its inputs. -/
def Target : Prop :=
  Schoenfeld1976.PsiThetaLog → Schoenfeld1976.PsiCert →
    MoebiusInputs.MertensSqrt → MoebiusInputs.SmallMoebiusSum →
    LambdaInputs.WeightSumBound → LambdaInputs.GHBounds →
    FiniteRH 1894438.5122 → RamareMoebius

end TernaryGoldbach.RSBounds.Moebius003
