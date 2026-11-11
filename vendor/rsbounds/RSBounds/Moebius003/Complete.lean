/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Final
import MoebiusCert.Final

/-!
# `RamareMoebius` from finite RH alone

`ramareMoebius` with (M) and (m) supplied by the kernel-checked computations of `MoebiusCert`
(`MoebiusInputs.mertensSqrt`, `MoebiusInputs.smallMoebiusSum`). The only premise left is
`FiniteRH 1894438.5122`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Goals

/-- Upstream's `RamareMoebius`: `|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`, from
`FiniteRH 1894438.5122`. -/
theorem ramareMoebius_of_finiteRH (hRH : FiniteRH 1894438.5122) : RamareMoebius :=
  ramareMoebius MoebiusInputs.mertensSqrt MoebiusInputs.smallMoebiusSum hRH

end TernaryGoldbach.RSBounds.Moebius003
