import TernaryGoldbach.Prelim.MoebiusDecay
import TernaryGoldbach.Prelim.MoebiusProfile

variable [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens]

/-!
# `|∑_{n≤x} μ(n)/n| ≤ 0.55/(log x − 0.7521)` for `x ≥ 10¹⁰`

The `q = 1` input for [H, (2.22)] (Ramaré's Liouville route, hal-02572851, in
`LiouvilleBound.lean`). It follows from `|∑_{n≤x} μ(n)/n| ≤ 0.09/log x` for `x ≥ 10¹⁰`
(`abs_m_le_009`, `MoebiusProfile.lean`).
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach.Prelim

omit [Fact TernaryGoldbach.PlattGRH] [Fact TernaryGoldbach.CDEMertens] in
theorem sqrt2_bounds : (1.414213 : ℝ) ≤ √2 ∧ √2 ≤ 1.414214 := by
  refine ⟨Real.le_sqrt_of_sq_le (by norm_num), ?_⟩
  calc √2 ≤ √(1.414214 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 1.414214 := Real.sqrt_sq (by norm_num)

/-- **Uniform Möbius bound** (`q = 1`): `|∑_{n ≤ x} μ(n)/n| ≤ 0.55/(log x − 0.7521)` for
`x ≥ 10¹⁰`, from `abs_m_le_009`. -/
theorem abs_sum_moebius_div_le {x : ℝ} (hx : 1e10 ≤ x) :
    |∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) / n| ≤ 0.55 / (Real.log x - 0.7521) := by
  have hlx := log_ge_23 (x := x) (by norm_num at hx ⊢; linarith)
  refine (abs_m_le_009 hx).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end TernaryGoldbach.Prelim
