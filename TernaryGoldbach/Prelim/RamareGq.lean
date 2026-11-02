import Mathlib

/-!
# Definitions for Ramaré's estimate for `G_d(R) = ∑_{r ≤ R, (r,d)=1} μ²(r)/φ(r)` ([Ram95, Lemma 3.4] = [H, (12.12)])

The estimate itself is `Prelim.ramare_Gq` (`Ramare.lean`), proved in `Ramare*.lean`. The definitions
agree with `MinorArcs.Gq`, `Sq`, `f1q`.
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

/-- `f₁(q) = ∏_{p ∣ q} f₁(p)` [H, (12.13)]. -/
noncomputable def f1qP (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, f1pP p

end TernaryGoldbach.Prelim
