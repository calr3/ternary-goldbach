/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.TargetL
import RSBounds.Schoenfeld1976Final

/-!
# `RamareMoebius` from (M), (m) and finite RH

`target_L` with (S) and (P) supplied by `Schoenfeld1976Final`: (S) is `psiThetaLog` (Theorem 7*,
(5.6b*)), and (P) is `psiCert`, the kernel-checked `|ψ(x) − x| ≤ (4/5)√x` on `[1500, 10¹⁰]`. The
premises left are the two finite computations on `μ` (`MoebiusInputs.MertensSqrt`,
`MoebiusInputs.SmallMoebiusSum`) and `FiniteRH 1894438.5122`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Goals

/-- Upstream's `RamareMoebius`: `|∑_{n ≤ x} μ(n)/n| ≤ 0.03/log x` for `x ≥ 11815`, from (M), (m)
and `FiniteRH 1894438.5122`. -/
theorem ramareMoebius (hM : MoebiusInputs.MertensSqrt) (hm : MoebiusInputs.SmallMoebiusSum)
    (hRH : FiniteRH 1894438.5122) : RamareMoebius :=
  target_L Schoenfeld1976Final.psiThetaLog Schoenfeld1976Final.psiCert hM hm hRH

end TernaryGoldbach.RSBounds.Moebius003
