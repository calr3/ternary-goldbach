import TernaryGoldbach.MinorArcs.TypeI

/-!
# The pointwise minor-arc bound [B, Theorem 3.1.1] — blueprint statement

The main result of Part I of [B]: for `η = η₂` and `2α = a/q + δ/x`, an explicit bound on
`|S_η(α, x)|` that is essentially `x (log q)/√φ(q)`.  Part I (Chs. 3–6) is its proof; it is
used in [B, Chs. 11, 13] to bound the minor-arc integral (14.49).

**Blueprint node: stated with `sorry`, not yet used by `ternary_goldbach`.**
-/

open Real

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 S)

/-- `R_{x,t} = 0.27125 log(1 + log(4t) / (2 log(9x^{1/3}/(2.004 t)))) + 0.41415` [B, (3.3)]. -/
noncomputable def R (x t : ℝ) : ℝ :=
  0.27125 * Real.log (1 + Real.log (4 * t) /
    (2 * Real.log (9 * x ^ (1 / 3 : ℝ) / (2.004 * t)))) + 0.41415

/-- `L_{x,t,q} = (q/φ(q)) (13/4 log t + 7.82) + 13.66 log t + 37.55` [B, (3.3)]. -/
noncomputable def L (t : ℝ) (q : ℕ) : ℝ :=
  q / Nat.totient q * (13 / 4 * Real.log t + 7.82) + 13.66 * Real.log t + 37.55

/-- **[B, Theorem 3.1.1]** Let `x ≥ 2.16 · 10²⁰`, `η = η₂`, `2α = a/q + δ/x` with `q ≤ Q`,
`(a, q) = 1`, `|δ/x| ≤ 1/qQ`, `Q = (3/4) x^{2/3}`.  Write `δ₀ = max(2, |δ|/4)`. -/
theorem theorem_3_1_1 {α x δ : ℝ} {a : ℤ} {q : ℕ} (hx : 2.16e20 ≤ x)
    (h : Approx2 α x δ a q (3 / 4 * x ^ (2 / 3 : ℝ))) :
    let δ₀ := max 2 (|δ| / 4)
    ((q : ℝ) ≤ x ^ (1 / 3 : ℝ) / 6 →
      ‖S eta2 x α‖ ≤
        (R x (δ₀ * q) * Real.log (δ₀ * q) + 0.5) / √(δ₀ * Nat.totient q) * x +
          2.5 * x / √(δ₀ * q) + 2 * x / (δ₀ * q) * L (δ₀ * q) q + 3.36 * x ^ (5 / 6 : ℝ)) ∧
    (x ^ (1 / 3 : ℝ) / 6 < q →
      ‖S eta2 x α‖ ≤
        0.276 * x ^ (5 / 6 : ℝ) * Real.log x ^ (3 / 2 : ℝ) + 1234 * x ^ (2 / 3 : ℝ) * Real.log x) := by
  sorry

end TernaryGoldbach.MinorArcs
