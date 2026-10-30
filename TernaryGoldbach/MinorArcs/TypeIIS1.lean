import TernaryGoldbach.MinorArcs.TypeII

/-!
# Type II sums [B, §5.1]: the sum `S₁` (blueprint)

`S₁(U, W) = ∑_{max(U, x/2W) < m ≤ x/W, m odd} (∑_{d > U, d | m} μ(d))²` [B, (5.6)], `v = 2`.

[B, §5.1] shows `S₁(U, W) = (x/W) H₂(x/WU) + O*(1.27 ζ(3/2)³ x^{3/2}/(W^{3/2} U))` (5.34), where
`H₂` comes from the triple sum `T₂(S) = ∑_{s ≤ S odd} (1/s) ∫_{1/2}^1 g₂(uS/s) du` (5.28),
`g₂(t) = ∑_{r₁, r₂ ≤ t, (r₁, r₂) = 1, r₁r₂ odd} μ(r₁)μ(r₂)/(σ(r₁)σ(r₂))` (Lemma 5.1.2).

**Status: statements only** (`sorry`). Plan (see `NOTES.md`): the reduction (5.7)–(5.8) and
Lemma 5.1.1 can be proved; Lemma 5.1.2's range `x ≤ 10⁶` and the numerics (5.31)–(5.32) are
computations, to become labelled trusted facts.
-/

open Real Finset
open ArithmeticFunction (moebius sigma)
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma

namespace TernaryGoldbach.MinorArcs

/-- `S₁(U, W)` [B, (5.6)] with `v = 2`. -/
noncomputable def S1 (x U W : ℝ) : ℝ :=
  ∑ m ∈ Ioc ⌊max U (x / (2 * W))⌋₊ ⌊x / W⌋₊,
    if Odd m then (∑ d ∈ m.divisors.filter (fun d : ℕ => U < (d : ℝ)), (μ d : ℝ)) ^ 2 else 0

/-- `g₂(t)` [B, Lemma 5.1.2]. -/
noncomputable def g2 (t : ℝ) : ℝ :=
  ∑ r₁ ∈ Icc 1 ⌊t⌋₊, ∑ r₂ ∈ Icc 1 ⌊t⌋₊,
    if Nat.Coprime r₁ r₂ ∧ Odd (r₁ * r₂) then
      (μ r₁ : ℝ) * μ r₂ / ((σ 1 r₁ : ℝ) * σ 1 r₂) else 0

/-- The triple sum `T₂(S) = ∑_{s ≤ S odd} (1/s) ∫_{1/2}^1 g₂(uS/s) du` [B, (5.28)]. -/
noncomputable def T2 (S : ℝ) : ℝ :=
  ∑ s ∈ Icc 1 ⌊S⌋₊, if Odd s then (1 / s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, g2 (u * S / s) else 0

/-- `H₂(S)` [B, (5.35)]: `(4/π²) T₂(S)` for `S < 16`, `0.15107` for `S ≥ 16`. -/
noncomputable def H2 (S : ℝ) : ℝ := if S < 16 then 4 / π ^ 2 * T2 S else 0.15107

/-- **[B, (5.34)]** (statement). -/
theorem S1_bound {x U W : ℝ} (hx : 0 < x) (hU : 0 < U) (hW : 0 < W) :
    S1 x U W ≤ x / W * H2 (x / (W * U)) +
      1.27 * (riemannZeta (3 / 2)).re ^ 3 * x ^ (3 / 2 : ℝ) / (W ^ (3 / 2 : ℝ) * U) := by
  sorry

/-- **[B, (5.36)]** (statement). -/
theorem integral_H2_le {T : ℝ} (hT : 1 ≤ T) :
    ∫ S in (1 : ℝ)..T, H2 S / S ≤ 0.15107 * Real.log T := by
  sorry

/-- **[B, (5.37)]** (statement). -/
theorem H2_le (S : ℝ) : H2 S ≤ 2 / π ^ 2 := by
  sorry

end TernaryGoldbach.MinorArcs
