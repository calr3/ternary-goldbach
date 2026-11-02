import TernaryGoldbach.Prelim.RamareNum

/-!
# Ramaré's estimate for `G_d(R)` ([Ram95, Lemma 3.4] = [H, (12.12)])

For all `d ≥ 1` and `R ≥ 1`,
`G_d(R) = (φ(d)/d)(log R + c_E + ∑_{p ∣ d} log p/p) + O*(7.284 R^{−1/3} f₁(d))`, where
`c_E = γ + ∑_p log p/(p(p−1)) = 1.332582275…`.

The proof follows Ramaré's method, with one change. `G_d = h_d ∗ v`, where `v(n) = [n odd]/n`
and `h_d` is multiplicative with `h_d(p^e) = 0` for `e ≥ 3` (`RamareConv`). Then
`∑_{b ≤ x, b odd} 1/b = ½ log x + (γ + log 2)/2 + O*(0.64 x^{−1/3})` (`RamareFo`), and
`∑_a |h_d(a)| a^{1/3} ≤ 11 f₁(d)` (`RamareBound`). Together these give the error term
`7.04 R^{−1/3} f₁(d) ≤ 7.284 R^{−1/3} f₁(d)` (`RamareMain`, `RamareLog`).

The change is in the second bound. [Ram95, (3.9)] states
`∏_p (1 + (p^{1/3} + p^{2/3})/(p(p−1))) ≤ 8`, but this product is `≈ 8.0845`. `RamareBound` instead
works with the exact local factors at `2` and evaluates the product over primes `≤ 1000` with the
kernel. The constant `c_E` is evaluated in `RamareNum` (`cR_bounds`).

Both [MV73, Lemma 7] (`MVLemma7.lean`) and [H, Prop 12.2.4] (`MinorArcs/LSQuot*.lean`) use this.
-/

namespace TernaryGoldbach.Prelim

/-- **Ramaré's estimate** [Ram95, Lemma 3.4], [H, (12.12)–(12.14)]. -/
theorem ramare_Gq : ∃ c : ℝ, 1.3325822 ≤ c ∧ c ≤ 1.3325823 ∧ ∀ d : ℕ, 1 ≤ d → ∀ R : ℝ, 1 ≤ R →
    |GqP d R - (Nat.totient d / d) * (Real.log R + c + SqP d)| ≤ 7.284 * R ^ (-(1 / 3 : ℝ)) * f1qP d :=
  ⟨RamPf.cR, RamPf.cR_bounds.1, RamPf.cR_bounds.2, fun _ hd _ hR =>
    RamPf.ramare_bound hd (by linarith)⟩

end TernaryGoldbach.Prelim
