import TernaryGoldbach.Helfgott.Defs
import TernaryGoldbach.CircleMethod

/-!
# The ℓ² norm over major arcs: a large sieve for primes [H, Ch. 12]

For `aₙ` supported on primes `> √x`, `S(α) = Σ aₙ e(αn)`:

* **Prop 12.1.2** (`prop_12_1_2`, proved in `LargeSieveProof.lean`).
* **Prop 12.2.4** (`prop_12_2_4`, proved in `LSQuot1.lean`–`LSQuot6.lean`): the quotient bound
  `G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + 1.36)/(log Q + c_E)`.
* **Cor 12.2.5, (12.42)** (`cor_12_2_5`, `LargeSieveProof.lean`): proved from the two.

`c_E = γ + Σ_p log p/(p(p − 1)) = 1.3325822…` [H, (12.14)]; we state everything with the smaller
`1.33258`, which only weakens the bounds.  `G_q(R) = Σ_{r ≤ R, (r,q)=1} μ²(r)/φ(r)` (12.2).

The arcs `𝔐_{δ₀,Q₀}` are `majorArcs δ₀ Q₀ x` [H, (10.5)], restricted to `(0, 1]`.
-/

open MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs)
open TernaryGoldbach (expTsum)

/-- `G_q(R) = Σ_{r ≤ R, (r, q) = 1} μ²(r)/φ(r)` [H, (12.2)]. -/
noncomputable def Gq (q : ℕ) (R : ℝ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q), ((μ r : ℝ) ^ 2) / Nat.totient r

/-- `c_E` rounded down. -/
def cE : ℝ := 1.33258

/-- The hypotheses on `aₙ` in [H, Props. 12.1.1, 12.1.2]: supported on primes `> √x`, in `ℓ¹`. -/
def PrimeSupported (x : ℝ) (a : ℕ → ℂ) : Prop :=
  (∀ n, a n ≠ 0 → n.Prime ∧ √x < n) ∧ Summable fun n => ‖a n‖


end TernaryGoldbach.MinorArcs
