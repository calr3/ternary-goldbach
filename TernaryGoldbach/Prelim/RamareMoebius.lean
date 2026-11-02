import Mathlib

/-!
# Ramaré's bound `|∑_{n≤x} μ(n)/n| ≤ 0.03/log x` ([H, (2.21)])

A published result, stated for `x ≥ 11815` as in [Ram13, Cor. 1.4]. Its uses are the uniform Möbius
bound of `MoebiusBound.lean` (for [H, (2.22)]), the Liouville bound of `LiouvilleBound.lean`, and
[H, Lemma 5.1.2] (`MinorArcs/G2Bound.lean`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- **Published result**: `|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`.
* O. Ramaré, *From explicit estimates for primes to explicit estimates for the Moebius function*,
  Acta Arith. 157 (2013), 365–379, Cor. 1.4: this bound for `x ≥ 11815`, as cited in [H, (2.21)];
* O. Ramaré, *Explicit estimates on several summatory functions involving the Moebius function*,
  Math. Comp. 84 (2015), Thm 1.2: `|m(X)| ≤ (0.0144 log X − 0.1)/(log X)²` for `X ≥ 463 421`,
  re-derived in O. Ramaré, S. Zuniga-Alterman, arXiv:2408.05969, which also proves
  `|m(X)| ≤ 0.010032/log X` for `X ≥ 617 990` (Cor. 1.2). -/
axiom ramare_moebius {x : ℝ} (hx : 11815 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 0.03 / Real.log x

end TernaryGoldbach.Prelim
