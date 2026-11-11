/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/

import RSBounds.LambdaCert.States

/-!
# Kernel checks of segments 20–38 (`n` from 5623 to 53248)
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

theorem seg20 : checkSeg st19 st20 = true := by decide +kernel

theorem seg21 : checkSeg st20 st21 = true := by decide +kernel

theorem seg22 : checkSeg st21 st22 = true := by decide +kernel

theorem seg23 : checkSeg st22 st23 = true := by decide +kernel

theorem seg24 : checkSeg st23 st24 = true := by decide +kernel

theorem seg25 : checkSeg st24 st25 = true := by decide +kernel

theorem seg26 : checkSeg st25 st26 = true := by decide +kernel

theorem seg27 : checkSeg st26 st27 = true := by decide +kernel

theorem seg28 : checkSeg st27 st28 = true := by decide +kernel

theorem seg29 : checkSeg st28 st29 = true := by decide +kernel

theorem seg30 : checkSeg st29 st30 = true := by decide +kernel

theorem seg31 : checkSeg st30 st31 = true := by decide +kernel

theorem seg32 : checkSeg st31 st32 = true := by decide +kernel

theorem seg33 : checkSeg st32 st33 = true := by decide +kernel

theorem seg34 : checkSeg st33 st34 = true := by decide +kernel

theorem seg35 : checkSeg st34 st35 = true := by decide +kernel

theorem seg36 : checkSeg st35 st36 = true := by decide +kernel

theorem seg37 : checkSeg st36 st37 = true := by decide +kernel

theorem seg38 : checkSeg st37 st38 = true := by decide +kernel

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
