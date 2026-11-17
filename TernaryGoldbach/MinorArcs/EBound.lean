import RSBounds.HelfgottAppA.EBound
import TernaryGoldbach.Prelim.LambdaMu

/-!
# [H, (14.28)]: `E ≤ 8.4029·10⁻¹² x`

`E = ∑_{n ≤ √x or n not prime} Λ(n)² η₊(n/x)²`. [H, §13.2, (14.28)]: `E ≤ (2.94325 log x + 5.12426) √x
≤ 8.4029·10⁻¹² x` for `x ≥ 4.9·10²⁶`. The proof is Helfgott's (Garald1/RSBounds,
`RSBounds/HelfgottAppA/`): the sup norms of Appendix A, `|η₊|_∞ ≤ 1.079955` and `|η₊ · t|_∞ ≤ 1.19073`
([H, (14.3), (14.24)]), a non-increasing majorant of `η₊(t/x)²` and summation by parts against
`∑_{n ≤ t, n not prime} Λ(n)² ≤ 1.4262 √t log t`. Its inputs `ψ(n) ≤ 1.03883 n` and
`ψ(y) − θ(y) < 1.4262 √y` ([H, (2.15), (5.5)]) are ours (`Prelim/LambdaMu.lean`).
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (etaPlus)

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **[H, (14.28)]**: `E ≤ 8.4029·10⁻¹² x` for `x ≥ 4.9·10²⁶`. -/
theorem E_le_14_28 {x : ℝ} (hx : 4.9e26 ≤ x) :
    ∑' n : ℕ, (if n.Prime ∧ √x < n then 0 else (Λ n * etaPlus (n / x)) ^ 2) ≤ 8.4029e-12 * x :=
  _root_.RSBounds.HelfgottAppA.E_le_14_28_book (fun n => (Prelim.psi_bounds n).1)
    (fun _ hy => Prelim.sum_vonMangoldt_nonprime_lt hy) hx

end TernaryGoldbach.MinorArcs
