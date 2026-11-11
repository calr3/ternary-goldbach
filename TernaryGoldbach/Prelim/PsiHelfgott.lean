import TernaryGoldbach.Statement
import RSBounds.Moebius003.Upstream
import RSBounds.HelfgottPsiBoundsFinal

/-!
# [H, (2.14)] and [H, (2.17)] with [H]'s constants

`ψ(y) ≤ 1.0004 y` and `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y ≥ 2.5·10⁷`, from `PlattGRH`.
The proofs are Helfgott's (Garald1/RSBounds, `RSBounds.HelfgottPsiBoundsFinal`, vendored unchanged
under `vendor/rsbounds/`):
* on `[2.5·10⁷, 10¹⁰]`, PsiCert: the kernel-checked `|ψ(x) − x| ≤ 0.8√x` on `[1500, 10¹⁰]`
  (`PsiFinite.psi_abs_sub_le_four_fifths_sqrt`);
* above `e²³ < 10¹⁰`, Rosser–Schoenfeld (1975): `|ψ(x) − x| < 0.00020211 x`, from RH up to height
  `1894438.5122` (`RosserSchoenfeld1975.psi_error_b23`);
* (2.17) from these by Abel summation.
RH up to `1894438.5122` follows from `PlattGRH` at `q = 1` (`Explicit.rh_upto_1e8`;
`RSBounds.Moebius003.finiteRH_of_plattGRH`).

`Prelim/LambdaMu.lean` keeps our own proofs with the weaker constants `1.0064`, `1.022`
(`sum_vonMangoldt_le_10064`, `sum_vonMangoldt_mul_lt_1022`), from `psi_two_sided` alone.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **[H, (2.14)]**: `ψ(y) ≤ 1.0004 y` for `y ≥ 2.5·10⁷` (the minor arcs use it at
`V ≥ 2.7·10⁷`). -/
theorem sum_vonMangoldt_le_a14 {y : ℝ} (hy : 2.5e7 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y :=
  TernaryGoldbach.RSBounds.HelfgottPsiBoundsFinal.sum_vonMangoldt_le_a14
    (TernaryGoldbach.RSBounds.Moebius003.finiteRH_of_plattGRH Fact.out) hy

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **[H, (2.17)]**: `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y ≥ 2.5·10⁷` (the minor arcs use it
at `y ≥ 2.7·10⁷`). -/
theorem sum_vonMangoldt_mul_lt_a17 {y : ℝ} (hy : 2.5e7 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 :=
  TernaryGoldbach.RSBounds.HelfgottPsiBoundsFinal.sum_vonMangoldt_mul_lt_a17
    (TernaryGoldbach.RSBounds.Moebius003.finiteRH_of_plattGRH Fact.out) hy

end TernaryGoldbach.Prelim
