/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Complete
import TernaryGoldbach.Statement
import TernaryGoldbach.Explicit.ZetaZeroSums

/-!
# Upstream's `RamareMoebius` from upstream's `PlattGRH`

calr3/ternary-goldbach (at `192ca57`) takes three hypotheses: `PlattGRH`, `BinaryGoldbachInput` and
`RamareMoebius`. Upstream proves RH up to `10⁸` from `PlattGRH` at `q = 1`
(`TernaryGoldbach.Explicit.rh_upto_1e8`), which gives `FiniteRH 1894438.5122`, the only premise of
`ramareMoebius_of_finiteRH`. So `RamareMoebius` follows from `PlattGRH`, and nothing is added.

`TernaryGoldbach.RamareMoebius` and `Moebius003.RamareMoebius` have the same body, so they are
equal by unfolding.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

/-- `PlattGRH` at `q = 1` gives RH up to `10⁸`, hence up to `1894438.5122`. -/
theorem finiteRH_of_plattGRH (h : TernaryGoldbach.PlattGRH) : Goals.FiniteRH 1894438.5122 := by
  have : Fact TernaryGoldbach.PlattGRH := ⟨h⟩
  intro ρ hz h0 h1 him
  exact TernaryGoldbach.Explicit.rh_upto_1e8 ρ hz h0 h1 (him.trans (by norm_num))

/-- **Upstream's `RamareMoebius`, from upstream's `PlattGRH`.** -/
theorem ramareMoebius_of_plattGRH (h : TernaryGoldbach.PlattGRH) : TernaryGoldbach.RamareMoebius :=
  ramareMoebius_of_finiteRH (finiteRH_of_plattGRH h)

end TernaryGoldbach.RSBounds.Moebius003
