/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Main
import RSBounds.LambdaInputsProof

/-!
# `Target` with the input (L) discharged

(L) is `LambdaInputs.weightSumBound` and `LambdaInputs.ghBounds`, the kernel-checked von Mangoldt
computations of `RSBounds/LambdaInputsProof.lean`. What remains are (S), (P), (M), (m) and finite RH.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open Goals

/-- The note's theorem from (S), (P), (M), (m) and `FiniteRH 1894438.5122`. -/
theorem target_L : Schoenfeld1976.PsiThetaLog → Schoenfeld1976.PsiCert →
    MoebiusInputs.MertensSqrt → MoebiusInputs.SmallMoebiusSum →
    FiniteRH 1894438.5122 → RamareMoebius :=
  fun hS hP hM hm hRH =>
    target hS hP hM hm LambdaInputs.weightSumBound LambdaInputs.ghBounds hRH

end TernaryGoldbach.RSBounds.Moebius003
