import TernaryGoldbach.MinorArcs.NumericsAsymp

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.PlattGRH]
  [Fact TernaryGoldbach.ButhePsi] [Fact TernaryGoldbach.RamareMoebius]

/-!
# `numerics_M`: the numerical inequality of the repaired minor-arc bound, for all `x ≥ 4.9·10²⁶`

Cells `cell0`–`cell8` (generated, `scripts/gen_cells.py`) cover `x ∈ [4.9·10²⁶, 4.9·10¹⁰¹]`;
`asymp_goal` covers `x ≥ 4.9·10¹⁰¹`. Proved, with no `sorry`.
-/

namespace TernaryGoldbach.MinorArcs

theorem numerics_M {x : ℝ} (hx : 4.9e26 ≤ x) : NumericsGoal x := by
  unfold NumericsGoal
  rcases le_or_gt x 1.47e27 with h0 | h0
  · exact cell0 (by linarith) (by linarith)
  rcases le_or_gt x 4.9e27 with h1 | h1
  · exact cell1 (by linarith) (by linarith)
  rcases le_or_gt x 4.9e28 with h2 | h2
  · exact cell2 (by linarith) (by linarith)
  rcases le_or_gt x 4.9e29 with h3 | h3
  · exact cell3 (by linarith) (by linarith)
  rcases le_or_gt x 4.9e31 with h4 | h4
  · exact cell4 (by linarith) (by linarith)
  rcases le_or_gt x 4.9e35 with h5 | h5
  · exact cell5 (by linarith) (by linarith)
  rcases le_or_gt x 4.9e43 with h6 | h6
  · exact cell6 (by linarith) (by linarith)
  rcases le_or_gt x 4.9e59 with h7 | h7
  · exact cell7 (by linarith) (by linarith)
  rcases le_or_gt x 4.9e101 with h8 | h8
  · exact cell8 (by linarith) (by linarith)
  exact asymp_goal h8.le

end TernaryGoldbach.MinorArcs
