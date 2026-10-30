import TernaryGoldbach.Helfgott.Defs
import TernaryGoldbach.CircleMethod

/-!
# The ℓ² norm over major arcs: a large sieve for primes [B, Ch. 12]

For `aₙ` supported on primes `> √x`, `S(α) = Σ aₙ e(αn)`:

* **Prop 12.1.2** (`prop_12_1_2`, blueprint node, `sorry`): `∫_{𝔐_{δ₀,Q₀}} |S|² ≤ C Σ|aₙ|²` whenever
  `G_q(2Q₀/sq) ≤ C G_q(2Q/sq)` for all even `q ≤ 2Q₀` and `s ∈ [1, 2Q₀/q]`, `Q = √(x/2δ₀)`.
  Its proof ([B, §12.1], after [Bom74, Thm. 7A]) needs Gauss sums of imprimitive characters.
* **Prop 12.2.4** (`prop_12_2_4`, **trusted computation**, `sorry`): the quotient bound
  `G_q(Q₀/sq)/G_q(Q/sq) ≤ (log Q₀ + 1.36)/(log Q + c_E)`.  [B]'s proof ends in a large interval-
  arithmetic computation ("about two weeks of computing", [B, p. 242, fn. 2]).
* **Cor 12.2.5, (12.42)** (`cor_12_2_5`): proved from the two.

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

/-- **[B, Prop. 12.1.2]** (blueprint node).  Let `δ₀ ≥ 1`, `Q₀ ≥ 1`, `δ₀Q₀² ≤ x/2`,
`Q = √(x/2δ₀)`.  If `G_q(2Q₀/sq) ≤ C G_q(2Q/sq)` for every even `q ≤ 2Q₀` and `1 ≤ s ≤ 2Q₀/q`,
then `∫_{𝔐_{δ₀,Q₀}} |S(α)|² dα ≤ C Σ|aₙ|²`. -/
theorem prop_12_1_2 {x δ₀ Q₀ C : ℝ} {a : ℕ → ℂ} (ha : PrimeSupported x a)
    (hδ₀ : 1 ≤ δ₀) (hQ₀ : 1 ≤ Q₀) (hx : δ₀ * Q₀ ^ 2 ≤ x / 2)
    (hC : ∀ q : ℕ, 1 ≤ q → Even q → (q : ℝ) ≤ 2 * Q₀ → ∀ s : ℝ, 1 ≤ s → s ≤ 2 * Q₀ / q →
      Gq q (2 * Q₀ / (s * q)) ≤ C * Gq q (2 * √(x / (2 * δ₀)) / (s * q))) :
    ∫ α in Ioc (0 : ℝ) 1 ∩ majorArcs δ₀ Q₀ x, ‖expTsum a α‖ ^ 2 ≤ C * ∑' n, ‖a n‖ ^ 2 := by
  sorry

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

/-- **[B, Cor. 12.2.5, (12.42)]**.  Let `Q₀ ≥ 10⁵`, `δ₀ ≥ 1`, `(20000 Q₀)² ≤ x/2δ₀`,
`Q = √(x/2δ₀)`, `2Q₀ ≤ (2Q)^{0.6}`.  Then
`∫_{𝔐_{δ₀,Q₀}} |S|² ≤ (log 2Q₀ + 1.36)/(log 2Q + c_E) Σ|aₙ|²`. -/
theorem cor_12_2_5 {x δ₀ Q₀ : ℝ} {a : ℕ → ℂ} (ha : PrimeSupported x a)
    (hQ₀ : 1e5 ≤ Q₀) (hδ₀ : 1 ≤ δ₀) (hx : (20000 * Q₀) ^ 2 ≤ x / (2 * δ₀))
    (hρ : 2 * Q₀ ≤ (2 * √(x / (2 * δ₀))) ^ (0.6 : ℝ)) :
    ∫ α in Ioc (0 : ℝ) 1 ∩ majorArcs δ₀ Q₀ x, ‖expTsum a α‖ ^ 2 ≤
      (Real.log (2 * Q₀) + 1.36) / (Real.log (2 * √(x / (2 * δ₀))) + cE) * ∑' n, ‖a n‖ ^ 2 := by
  set Q := √(x / (2 * δ₀)) with hQdef
  have hQ0 : 0 ≤ x / (2 * δ₀) := le_trans (by positivity) hx
  have hQsq : Q ^ 2 = x / (2 * δ₀) := Real.sq_sqrt hQ0
  have hQ : 20000 * Q₀ ≤ Q := by
    rw [hQdef]; exact Real.le_sqrt_of_sq_le hx
  refine prop_12_1_2 ha hδ₀ (by linarith) ?_ fun q hq _ hq2 s hs hsq => ?_
  · -- `δ₀ Q₀² ≤ x/2`
    have h1 : Q₀ ^ 2 ≤ x / (2 * δ₀) := le_trans (by nlinarith) hx
    have h2 : δ₀ * Q₀ ^ 2 ≤ δ₀ * (x / (2 * δ₀)) := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : δ₀ * (x / (2 * δ₀)) = x / 2 := by field_simp
    linarith
  · have h2Q₀ : (0 : ℝ) < 2 * Q₀ := by linarith
    have hlog : Real.log (2 * Q₀) ≤ 0.6 * Real.log (2 * Q) := by
      have := Real.log_le_log h2Q₀ hρ
      rwa [Real.log_rpow (by nlinarith)] at this
    exact prop_12_2_4 (by linarith) (by linarith) hlog hq hq2 hs hsq

end TernaryGoldbach.MinorArcs
