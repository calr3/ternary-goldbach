import Mathlib
import TernaryGoldbach.Prelim.MoebiusCoprime

/-!
# Explicit bounds on sums of `Λ` and `μ` [B, §2.5]

[B] quotes these from the literature (with some supplementary computations).  They are recorded
here as **trusted facts** (`sorry`), each with its source, and are used as hypotheses-free inputs
by the Type I estimates.  Only the bounds needed so far are listed; [B, §2.5] has more
((2.13), (2.14), (2.17)–(2.19), (2.21)–(2.24)).

Two remarks.
* (2.16) is only claimed for `y > 663` (it fails, e.g., at `y = 3`), so results that use it need
  that hypothesis.
* (2.20) is **proved** (elementarily) in `Prelim/MoebiusCoprime.lean`.
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

/-- **[B, (2.13)]** ([RS62, (3.21)] for `x > 1000` plus prime powers `≤ 1000`, and a computation
for `x ≤ 1000`): `∑_{n ≤ x} Λ(n)/n ≥ log x - log(3/√2)` for `x ≥ 1`. -/
theorem log_sub_le_sum_vonMangoldt_div {x : ℝ} (hx : 1 ≤ x) :
    Real.log x - Real.log (3 / √2) ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℝ) / n := by
  sorry

/-- **[B, (2.14)]** ([RR96, p. 423, second table] and a computation for `2·10⁶ ≤ y ≤ 4·10⁶`):
`∑_{n ≤ y} Λ(n) ≤ 1.0004 y` for `y ≥ 2·10⁶`. -/
theorem sum_vonMangoldt_le_10004 {y : ℝ} (hy : 2e6 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y := by
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

/-- **[B, (2.17)]** ([RR96, p. 423] and computations for `y < 10⁷`, partial summation):
`∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y > 1.6·10⁶`. -/
theorem sum_vonMangoldt_mul_lt' {y : ℝ} (hy : 1.6e6 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 := by
  sorry

/-- **[B, (2.18)]**: `∑_{n ≤ y} Λ(n)/√n < 2·1.0004 √y` for `y ≥ 1`. -/
theorem sum_vonMangoldt_div_sqrt_lt {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / √n < 2 * 1.0004 * √y := by
  sorry

/-- **[B, (2.19)]** ([RS75, Cor. 2] for `y ≥ 2·758699`, a computation for `117 ≤ y < 2·758699`):
`∑_{y/2 < p ≤ y} (log p)² ≤ (1/2) y log y` for `y ≥ 117`. -/
theorem sum_log_sq_primes_le {y : ℝ} (hy : 117 ≤ y) :
    ∑ p ∈ (Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y := by
  sorry

/-- **[B, (5.5)]** ([RS62, Thm. 13]): `ψ(y) - θ(y) = ∑_{n ≤ y, n not prime} Λ(n) < 1.4262 √y`
for `y > 0`. -/
theorem sum_vonMangoldt_nonprime_lt {y : ℝ} (hy : 0 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (if n.Prime then 0 else (Λ n : ℝ)) < 1.4262 * √y := by
  sorry

/-- **[B, (2.21)]** (Ramaré [Ram13]): `|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`. -/
theorem abs_sum_moebius_div_le_log {x : ℝ} (hx : 11815 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 0.03 / Real.log x := by
  sorry

/-- **[B, (2.22)]** (Ramaré [Ramb]): `|∑_{n ≤ x, (n,q)=1} μ(n)/n| ≤ (4/5)(q/φ(q))/log(x/q)` for
`q < x` (stated in [B] for `q ≤ x`; at `q = x` the right side is `+∞`). -/
theorem abs_sum_moebius_div_coprime_le_log {x : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqx : (q : ℝ) < x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n else 0)| ≤
      4 / 5 * (q / Nat.totient q) / Real.log (x / q) := by
  sorry

/-- **[B, (2.23)]** (Ramaré [Ramb]): `|∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n)| ≤ 1.00303 q/φ(q)`
for all `x > 0`, `q ≥ 1`. -/
theorem abs_sum_moebius_div_log_coprime_le {x : ℝ} (hx : 0 < x) {q : ℕ} (hq : 1 ≤ q) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0)| ≤
      1.00303 * (q / Nat.totient q) := by
  sorry

/-- **[B, (2.24)]** (a computation by Helfgott): `|∑_{n ≤ x} μ(n)/n| ≤ √(2/x)` for
`0 < x ≤ 10¹²`. -/
theorem abs_sum_moebius_div_le_sqrt {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1e12) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ √(2 / x) := by
  sorry

/-- **[B, Lemma C.2.2]** ([RS62, Thm. 15] for `q ≥ 27`, and `q/φ(q) ≤ 3 < Ϝ(r)` for `q < 27`):
`q/φ(q) < Ϝ(r) = e^γ log log r + 2.50637/log log r` for `q ≥ 1`, `r ≥ max(3, q)`. -/
theorem div_totient_lt {q : ℕ} (hq : 1 ≤ q) {r : ℝ} (hr : 3 ≤ r) (hqr : (q : ℝ) ≤ r) :
    (q : ℝ) / Nat.totient q < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) := by
  sorry

end TernaryGoldbach.Prelim
