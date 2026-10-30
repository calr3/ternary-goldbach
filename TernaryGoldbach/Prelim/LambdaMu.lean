import Mathlib

/-!
# Explicit bounds on sums of `Λ` and `μ` [B, §2.5]

[B] quotes these from the literature (with some supplementary computations).  They are recorded
here as **trusted facts** (`sorry`), each with its source, and are used as hypotheses-free inputs
by the Type I estimates.  Only the bounds needed so far are listed; [B, §2.5] has more
((2.13), (2.14), (2.17)–(2.19), (2.21)–(2.24)).

Two remarks.
* (2.16) is only claimed for `y > 663` (it fails, e.g., at `y = 3`), so results that use it need
  that hypothesis.
* (2.20) has an elementary proof for `q = 1` (from `∑_{n ≤ x} μ(n)⌊x/n⌋ = 1`); the general case is
  [GR96, Lemma 10.2].
-/

open Finset
open ArithmeticFunction (vonMangoldt moebius)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- **[B, (2.12)]** ([RS62, (3.23)] plus a computation for prime powers `< 32`):
`∑_{n ≤ x} Λ(n)/n ≤ log x` for `x ≥ 1`. -/
theorem sum_vonMangoldt_div_le_log {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℝ) / n ≤ Real.log x := by
  sorry

/-- **[B, (2.15)]** ([RS62, Thm. 12]): `ψ(y) = ∑_{n ≤ y} Λ(n) < 1.03883 y` for `y > 0`. -/
theorem sum_vonMangoldt_lt {y : ℝ} (hy : 0 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) < 1.03883 * y := by
  sorry

/-- **[B, (2.16)]** ((2.15) and partial summation for `y > 200000`, a computation for
`663 < y ≤ 200000`): `∑_{n ≤ y} Λ(n) n < 1.03884 y²/2` for `y > 663`. -/
theorem sum_vonMangoldt_mul_lt {y : ℝ} (hy : 663 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.03884 * y ^ 2 / 2 := by
  sorry

/-- **[B, (2.20)]** (Granville–Ramaré [GR96, Lemma 10.2]):
`|∑_{n ≤ x, (n, q) = 1} μ(n)/n| ≤ 1` for all `x` and all `q ≥ 1`. -/
theorem abs_sum_moebius_div_coprime_le_one (x : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤ 1 := by
  sorry

end TernaryGoldbach.Prelim
