/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Inputs

/-!
# §4 of the note: the range of the cells

`D_end = 306985·10⁶⁴ ≥ e¹⁶⁰` is the right end of the last of the 208 cells, and
`D_mid = 942467·10⁵³ ≈ e^{135.79}` is the left end of cell 173.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

/-- The right end of the last cell, `≥ e¹⁶⁰`. -/
def Dend : ℕ := 306985 * 10 ^ 64

/-- The left end of cell 173, `≤ D_end^{0.85}`. -/
def Dmid : ℕ := 942467 * 10 ^ 53

/-- What the 208 cells deliver: the profile bounds `ν̄ = 0.017` on `[X₀, D_end)` and
`ν_∞ = 0.014` on `[D_mid, D_end)` (hypotheses of Proposition 10), and the theorem itself on
`[X₀, D_end)` (Corollary 9 and outcome (iii)). -/
structure CellsResult : Prop where
  nuBar : ∀ n : ℕ, X0 ≤ n → n < Dend → |N n| ≤ 0.017 * n
  nuInf : ∀ n : ℕ, Dmid ≤ n → n < Dend → |N n| ≤ 0.014 * n
  mBound : ∀ n : ℕ, X0 ≤ n → n < Dend → |msum n| * Real.log (n + 1) ≤ 0.03


end TernaryGoldbach.RSBounds.Moebius003
