import TernaryGoldbach.Helfgott.Defs
import TernaryGoldbach.CircleMethod

/-!
# The ℓ² norm over major arcs: a large sieve for primes [B, Ch. 12]

For `aₙ` supported on primes `> √x`, `S(α) = Σ aₙ e(αn)`:

* **Prop 12.1.2** (`prop_12_1_2`, proved in `LargeSieveProof.lean`).
* **Prop 12.2.4** (`prop_12_2_4`, **trusted computation**, `sorry`): the quotient bound
  `G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + 1.36)/(log Q + c_E)`.  [B]'s proof ends in a large interval-
  arithmetic computation ("about two weeks of computing", [B, p. 242, fn. 2]).
* **Cor 12.2.5, (12.42)** (`cor_12_2_5`, `LargeSieveProof.lean`): proved from the two.

`c_E = γ + Σ_p log p/(p(p − 1)) = 1.3325822…` [B, (12.14)]; we state everything with the smaller
`1.33258`, which only weakens the bounds.  `G_q(R) = Σ_{r ≤ R, (r,q)=1} μ²(r)/φ(r)` (12.2).

The arcs `𝔐_{δ₀,Q₀}` are `majorArcs δ₀ Q₀ x` [B, (10.5)], restricted to `(0, 1]`.
-/

open MeasureTheory Set
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (majorArcs)
open TernaryGoldbach (expTsum)

/-- `G_q(R) = Σ_{r ≤ R, (r, q) = 1} μ²(r)/φ(r)` [B, (12.2)]. -/
noncomputable def Gq (q : ℕ) (R : ℝ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q), ((μ r : ℝ) ^ 2) / Nat.totient r

/-- `c_E` rounded down. -/
def cE : ℝ := 1.33258

/-- The hypotheses on `aₙ` in [B, Props. 12.1.1, 12.1.2]: supported on primes `> √x`, in `ℓ¹`. -/
def PrimeSupported (x : ℝ) (a : ℕ → ℂ) : Prop :=
  (∀ n, a n ≠ 0 → n.Prime ∧ √x < n) ∧ Summable fun n => ‖a n‖

/-- **[B, Prop. 12.2.4]** — **trusted computation**.  Let `Q ≥ 20000 Q₀`, `Q₀ ≥ 10⁵`,
`log Q₀ / log Q ≤ 0.6`.  Then for `1 ≤ q ≤ Q₀` and `1 ≤ s ≤ Q₀/q`,
`G_q(Q₀/sq) / G_q(Q/sq) ≤ (log Q₀ + 1.36)/(log Q + c_E)`.  [B]'s proof reduces this, via
Ramaré's (12.12) and explicit estimates, to a finite check of all `R ∈ [ϖ(q), λ(q))` for
`q < 3.3·10⁹` (and `q < 2.2·10¹⁰`, `210 ∣ q`) by interval arithmetic. -/
theorem prop_12_2_4 {Q Q₀ : ℝ} (hQ : 20000 * Q₀ ≤ Q) (hQ₀ : 1e5 ≤ Q₀)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) {q : ℕ} (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q₀) {s : ℝ}
    (hs : 1 ≤ s) (hsQ : s ≤ Q₀ / q) :
    Gq q (Q₀ / (s * q)) ≤ (Real.log Q₀ + 1.36) / (Real.log Q + cE) * Gq q (Q / (s * q)) := by
  sorry

end TernaryGoldbach.MinorArcs
