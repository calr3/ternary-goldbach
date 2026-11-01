import Mathlib

/-!
# Ramaré's estimate for `G_d(R) = ∑_{r ≤ R, (r,d)=1} μ²(r)/φ(r)` ([Ram95, Lemma 3.4] = [B, (12.12)])

Stated here (in `Prelim`) so that both [MV73, Lemma 7] (`MVLemma7.lean`) and [B, Prop 12.2.4]
(`MinorArcs/LSQuot*.lean`) can use it. The definitions agree with `MinorArcs.Gq`, `Sq`, `f1q`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- `G_q(R) = ∑_{r ≤ R, (r,q)=1} μ²(r)/φ(r)`. -/
noncomputable def GqP (q : ℕ) (R : ℝ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q), ((μ r : ℝ) ^ 2) / Nat.totient r

/-- `S_q = ∑_{p ∣ q} log p / p`. -/
noncomputable def SqP (q : ℕ) : ℝ := ∑ p ∈ q.primeFactors, Real.log p / p

/-- `(1 + p^{−2/3}) (1 + (p^{1/3} + p^{2/3})/(p(p−1)))⁻¹`. -/
noncomputable def f1pP (p : ℕ) : ℝ :=
  (1 + (p : ℝ) ^ (-(2 / 3 : ℝ))) /
    (1 + ((p : ℝ) ^ (1 / 3 : ℝ) + (p : ℝ) ^ (2 / 3 : ℝ)) / ((p : ℝ) * ((p : ℝ) - 1)))

/-- `f₁(q) = ∏_{p ∣ q} f₁(p)` [B, (12.13)]. -/
noncomputable def f1qP (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, f1pP p

/-- **Published result** (O. Ramaré, *On Šnirel'man's constant*, Ann. Scuola Norm. Sup. Pisa Cl.
Sci. (4) 22 (1995), 645–706, Lemma 3.4 and (3.6); [B, (12.12)–(12.14)]): for all `d ≥ 1` and
`R ≥ 1` (the paper: all `X > 0`),
`G_d(R) = (φ(d)/d)(log R + c_E + ∑_{p ∣ d} log p/p) + O*(7.284 R^{−1/3} f₁(d))`, where
`c_E = γ + ∑_p log p/(p(p−1)) = 1.332582275332…`. -/
axiom ramare_Gq : ∃ c : ℝ, 1.3325822 ≤ c ∧ c ≤ 1.3325823 ∧ ∀ d : ℕ, 1 ≤ d → ∀ R : ℝ, 1 ≤ R →
    |GqP d R - (Nat.totient d / d) * (Real.log R + c + SqP d)| ≤ 7.284 * R ^ (-(1 / 3 : ℝ)) * f1qP d

end TernaryGoldbach.Prelim
