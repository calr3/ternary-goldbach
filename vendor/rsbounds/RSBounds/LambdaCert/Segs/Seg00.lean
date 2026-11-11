/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/

import RSBounds.LambdaCert.States

/-!
# Kernel checks of segments 1–19 (`n` from 1 to 5623)
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

theorem seg1 : checkSeg st0 st1 = true := by decide +kernel

theorem seg2 : checkSeg st1 st2 = true := by decide +kernel

theorem seg3 : checkSeg st2 st3 = true := by decide +kernel

theorem seg4 : checkSeg st3 st4 = true := by decide +kernel

theorem seg5 : checkSeg st4 st5 = true := by decide +kernel

theorem seg6 : checkSeg st5 st6 = true := by decide +kernel

theorem seg7 : checkSeg st6 st7 = true := by decide +kernel

theorem seg8 : checkSeg st7 st8 = true := by decide +kernel

theorem seg9 : checkSeg st8 st9 = true := by decide +kernel

theorem seg10 : checkSeg st9 st10 = true := by decide +kernel

theorem seg11 : checkSeg st10 st11 = true := by decide +kernel

theorem seg12 : checkSeg st11 st12 = true := by decide +kernel

theorem seg13 : checkSeg st12 st13 = true := by decide +kernel

theorem seg14 : checkSeg st13 st14 = true := by decide +kernel

theorem seg15 : checkSeg st14 st15 = true := by decide +kernel

theorem seg16 : checkSeg st15 st16 = true := by decide +kernel

theorem seg17 : checkSeg st16 st17 = true := by decide +kernel

theorem seg18 : checkSeg st17 st18 = true := by decide +kernel

theorem seg19 : checkSeg st18 st19 = true := by decide +kernel

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
