/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.CellData

/-!
# §4 of the note: the induction on `[10⁹, D_end)`

The 208 cells of `cellData` are checked by the kernel (`decide +kernel`), and `checkCells_sound`
turns the check into `CellsResult`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

set_option maxRecDepth 1000000 in
/-- **The computation of §4**: all 208 cells pass. -/
theorem cells_check : checkCells st0 cellData = true := by decide +kernel

/-- Proposition 8, Corollary 9 and the computation of §4. -/
theorem cells (h : Inputs) : CellsResult := by
  obtain ⟨h1, h2, h3⟩ := checkCells_sound h cellData st0 st0_ok cells_check
  exact ⟨h1, h2, h3⟩

end TernaryGoldbach.RSBounds.Moebius003
