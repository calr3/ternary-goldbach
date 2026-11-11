import RSBounds.HelfgottPsiBounds
import RSBounds.Schoenfeld1976Final

/-!
# [H, (2.14)] and [H, (2.17)] with Helfgott's constants, PsiCert discharged

`HelfgottPsiBounds` with PsiCert supplied by the kernel-checked campaign
(`Schoenfeld1976Final.psiCert`, i.e. `PsiFinite.psi_abs_sub_le_four_fifths_sqrt`). The only premise
left is `FiniteRH 1894438.5122`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.HelfgottPsiBoundsFinal

open Goals

/-- **[H, (2.14)]**: `∑_{n ≤ y} Λ(n) ≤ 1.0004 y` for `y ≥ 2.5·10⁷`. -/
theorem sum_vonMangoldt_le_a14 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 2.5e7 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) ≤ 1.0004 * y :=
  HelfgottPsiBounds.sum_vonMangoldt_le_a14 Schoenfeld1976Final.psiCert hRH hy

/-- **[H, (2.17)]**: `∑_{n ≤ y} Λ(n) n < 1.0008 y²/2` for `y ≥ 2.5·10⁷`. -/
theorem sum_vonMangoldt_mul_lt_a17 (hRH : FiniteRH 1894438.5122) {y : ℝ} (hy : 2.5e7 ≤ y) :
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) * n < 1.0008 * y ^ 2 / 2 :=
  HelfgottPsiBounds.sum_vonMangoldt_mul_lt_a17 Schoenfeld1976Final.psiCert hRH hy

end TernaryGoldbach.RSBounds.HelfgottPsiBoundsFinal
