import TernaryGoldbach.Prelim.McheckRSBounds
import TernaryGoldbach.Prelim.McheckSmall
import TernaryGoldbach.Prelim.MoebiusLogCoprime
import TernaryGoldbach.Prelim.RamareMoebius

/-!
# [H, (2.23)] with [H]'s constant: `|∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n)| ≤ 1.00303 q/φ(q)`

[H] quotes it from Ramaré [Ramb, Cor. 1.10], who deduces it from `0 ≤ m̌(x) ≤ m̌(30)` (Balazard) by
the reduction of `MoebiusLogCoprime.lean`. We prove `|m̌(y)| ≤ 1.00303` for `y ≥ 1` by the kernel on
`[1, 2·10⁵]` (`McheckSmall.lean`) and from `|m̌(y) − 1| ≤ 0.00303` beyond (`McheckBig.lean`, with
RSBounds' inputs, which hold under `PlattGRH`). The proof uses the weaker `q/φ(q) + 2.67`
(`MoebiusLog.lean`), which suffices; this file records [H]'s statement.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

/-- RSBounds' `Inputs`, from `PlattGRH`. -/
theorem rsInputs_of_plattGRH (h : PlattGRH) : RSBounds.Moebius003.Inputs :=
  RSBounds.Moebius003.Inputs.of_target_hyps RSBounds.Schoenfeld1976Final.psiThetaLog
    RSBounds.Schoenfeld1976Final.psiCert RSBounds.MoebiusInputs.mertensSqrt
    RSBounds.MoebiusInputs.smallMoebiusSum RSBounds.LambdaInputs.weightSumBound
    RSBounds.LambdaInputs.ghBounds (RSBounds.Moebius003.finiteRH_of_plattGRH h)

/-- `|m̌(y)| ≤ 1.00303` for `y ≥ 1`. -/
theorem abs_mcheck_le (h : PlattGRH) {y : ℝ} (hy : 1 ≤ y) : |mcheck y| ≤ 1.00303 := by
  rcases le_or_gt y 200000 with hy2 | hy2
  · exact abs_mcheck_le_small hy hy2
  · have hI := mcheckBigInputs_of (rsInputs_of_plattGRH h) (ramareMoebius_of_plattGRH h)
      sum_abs_mertR_div_le
    have h1 := abs_mcheck_sub_one_le_big hI hy2.le
    calc |mcheck y| = |(mcheck y - 1) + 1| := by ring_nf
      _ ≤ |mcheck y - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 1.00303 := by rw [abs_one]; linarith

/-- **[H, (2.23)]** with [H]'s constant: `|∑_{n ≤ x, (n,q)=1} μ(n)/n · log(x/n)| ≤ 1.00303 q/φ(q)`
for `x > 0`, `q ≥ 1` (Ramaré [Ramb, Cor. 1.10]). -/
theorem abs_sum_moebius_div_log_coprime_le_sharp (h : PlattGRH) {x : ℝ} (hx : 0 < x) {q : ℕ}
    (hq : 1 ≤ q) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (if Nat.Coprime n q then (μ n : ℝ) / n * Real.log (x / n) else 0)| ≤
      1.00303 * (q / Nat.totient q) :=
  abs_sum_coprime_log_le_of_mcheck (fun _ hy => abs_mcheck_le h hy) hx hq

end TernaryGoldbach.Prelim
