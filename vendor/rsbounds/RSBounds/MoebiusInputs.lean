/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The two Möbius computations of `mobius003.tex`

Statements only; Mathlib-only. These are the hypotheses (M) and (m) of the proof of
`|∑_{n ≤ x} μ(n)/n| ≤ 0.03 / log x` for `x ≥ 11815` in `mobius003.tex` (8 November 2026).

* (M): `|M(n)| ≤ 0.571 √n` for `33 ≤ n ≤ 10⁹`, where `M(n) = ∑_{k ≤ n} μ(k)`, stated in integers
  (`0.571² = 0.326041`). The largest ratio is `0.567105`, at `n = 199`.
* (m): `|m(n)| log(n + 1) ≤ 0.03` for `11815 ≤ n ≤ 6·10⁵`, where `m(n) = ∑_{k ≤ n} μ(k)/k`. Since
  `m` is constant on `[n, n + 1)`, this is the real-variable statement on `[11815, 6·10⁵ + 1)`.
  The largest value is `0.029496`, at `n = 11820`.
-/

namespace TernaryGoldbach.RSBounds.MoebiusInputs

/-- (M): `10⁶ M(n)² ≤ 326041 n` for `33 ≤ n ≤ 10⁹`, i.e. `|M(n)| ≤ 0.571 √n`. -/
def MertensSqrt : Prop :=
  ∀ n : ℕ, 33 ≤ n → n ≤ 10 ^ 9 →
    10 ^ 6 * (∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k) ^ 2 ≤ 326041 * (n : ℤ)

/-- (m): `|m(n)| log(n + 1) ≤ 0.03` for `11815 ≤ n ≤ 6·10⁵`. -/
def SmallMoebiusSum : Prop :=
  ∀ n : ℕ, 11815 ≤ n → n ≤ 6 * 10 ^ 5 →
    |∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℝ) / k| * Real.log ((n : ℝ) + 1) ≤ 0.03

end TernaryGoldbach.RSBounds.MoebiusInputs
