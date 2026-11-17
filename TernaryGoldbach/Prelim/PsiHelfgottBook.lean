import TernaryGoldbach.Statement
import TernaryGoldbach.Prelim.LambdaMu
import RSBounds.Moebius003.Upstream
import RSBounds.HelfgottLowBook

/-!
# [H, (2.14)–(2.19)] on [H]'s ranges

[H, §2.3] states:
* (2.14) `ψ(y) ≤ 1.0004 y` for `y ≥ 2·10⁶`;
* (2.16) `∑_{n ≤ y} Λ(n) n < 1.03884 y²/2` for `y > 663`;
* (2.17) `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y > 1.6·10⁶`;
* (2.18) `∑_{n ≤ y} Λ(n)/√n < 2 · 1.0004 √y` for `y ≥ 1`;
* (2.19) `∑_{y/2 < p ≤ y} (log p)² ≤ ½ y log y` for `y ≥ 117`.

The minor arcs use (2.14) and (2.17) only for `y ≥ 2.7·10⁷` (`PsiHelfgott.lean`, from `2.5·10⁷`) and
(2.19) only for `y ≥ 2·10⁶` (`LambdaMu.sum_log_sq_primes_le`); they do not use (2.16) or (2.18).
This file records [H]'s statements on [H]'s ranges; the main theorems do not import it.

The proofs are Helfgott's (Garald1/RSBounds, a Lake dependency):
* (2.14), (2.17): `RSBounds.HelfgottPsiBoundsBook`. Above `4·10⁶` and `2.5·10⁷` they are
  `HelfgottPsiBoundsFinal`'s (as in `PsiHelfgott.lean`); below, an unconditional kernel-checked
  walk (`RSBounds.HelfgottSmall`).
* (2.16), (2.18): `RSBounds.HelfgottLowBook`, a kernel-checked walk up to `2·10⁶`
  (`RSBounds.HelfgottLow`) and, above, summation by parts from (2.17) and (2.14).
* (2.19): unconditional. `RSBounds.HelfgottLow.sum_log_sq_primes_le_small` covers
  `117 ≤ y < 2·10⁶ + 1` by a kernel-checked walk, and `LambdaMu.sum_log_sq_primes_le` covers
  `y ≥ 2·10⁶`.

The only premise of (2.14)–(2.18) is RH up to height `1894438.5122`, which follows from `PlattGRH`
at `q = 1` (`RSBounds.Moebius003.finiteRH_of_plattGRH`).
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim

/-- **[H, (2.14)]** on [H]'s range: `ψ(y) ≤ 1.0004 y` for `y ≥ 2·10⁶`. -/
theorem sum_vonMangoldt_le_a14_book (h : PlattGRH) {y : ℝ} (hy : 2e6 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y :=
  TernaryGoldbach.RSBounds.HelfgottPsiBoundsBook.sum_vonMangoldt_le_a14
    (TernaryGoldbach.RSBounds.Moebius003.finiteRH_of_plattGRH h) hy

/-- **[H, (2.16)]** on [H]'s range: `∑_{n ≤ y} Λ(n) n < 1.03884 y²/2` for `y > 663`. -/
theorem sum_vonMangoldt_mul_lt_a16_book (h : PlattGRH) {y : ℝ} (hy : 663 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.03884 * y ^ 2 / 2 :=
  TernaryGoldbach.RSBounds.HelfgottLowBook.sum_vonMangoldt_mul_lt_a16
    (TernaryGoldbach.RSBounds.Moebius003.finiteRH_of_plattGRH h) hy

/-- **[H, (2.17)]** on [H]'s range: `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y > 1.6·10⁶`. -/
theorem sum_vonMangoldt_mul_lt_a17_book (h : PlattGRH) {y : ℝ} (hy : 1.6e6 < y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 :=
  TernaryGoldbach.RSBounds.HelfgottPsiBoundsBook.sum_vonMangoldt_mul_lt_a17
    (TernaryGoldbach.RSBounds.Moebius003.finiteRH_of_plattGRH h) hy

/-- **[H, (2.18)]** on [H]'s range: `∑_{n ≤ y} Λ(n)/√n < 2 · 1.0004 √y` for `y ≥ 1`. -/
theorem sum_vonMangoldt_div_sqrt_lt_a18_book (h : PlattGRH) {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / √(n : ℝ) < 2 * 1.0004 * √y :=
  TernaryGoldbach.RSBounds.HelfgottLowBook.sum_vonMangoldt_div_sqrt_lt_a18
    (TernaryGoldbach.RSBounds.Moebius003.finiteRH_of_plattGRH h) hy

/-- **[H, (2.19)]** on [H]'s range: `∑_{y/2 < p ≤ y} (log p)² ≤ ½ y log y` for `y ≥ 117`. No
hypothesis is needed. -/
theorem sum_log_sq_primes_le_book {y : ℝ} (hy : 117 ≤ y) :
    ∑ p ∈ (Ioc ⌊y / 2⌋₊ ⌊y⌋₊).filter Nat.Prime, Real.log p ^ 2 ≤ 1 / 2 * y * Real.log y :=
  _root_.RSBounds.HelfgottLow.sum_log_sq_primes_le_of (fun _ h => sum_log_sq_primes_le h) hy

end TernaryGoldbach.Prelim
