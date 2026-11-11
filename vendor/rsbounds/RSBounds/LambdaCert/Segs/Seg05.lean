/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/

import RSBounds.LambdaCert.States

/-!
# Kernel checks of segments 96–114 (`n` from 262144 to 335872)
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

theorem seg96 : checkSeg st95 st96 = true := by decide +kernel

theorem seg97 : checkSeg st96 st97 = true := by decide +kernel

theorem seg98 : checkSeg st97 st98 = true := by decide +kernel

theorem seg99 : checkSeg st98 st99 = true := by decide +kernel

theorem seg100 : checkSeg st99 st100 = true := by decide +kernel

theorem seg101 : checkSeg st100 st101 = true := by decide +kernel

theorem seg102 : checkSeg st101 st102 = true := by decide +kernel

theorem seg103 : checkSeg st102 st103 = true := by decide +kernel

theorem seg104 : checkSeg st103 st104 = true := by decide +kernel

theorem seg105 : checkSeg st104 st105 = true := by decide +kernel

theorem seg106 : checkSeg st105 st106 = true := by decide +kernel

theorem seg107 : checkSeg st106 st107 = true := by decide +kernel

theorem seg108 : checkSeg st107 st108 = true := by decide +kernel

theorem seg109 : checkSeg st108 st109 = true := by decide +kernel

theorem seg110 : checkSeg st109 st110 = true := by decide +kernel

theorem seg111 : checkSeg st110 st111 = true := by decide +kernel

theorem seg112 : checkSeg st111 st112 = true := by decide +kernel

theorem seg113 : checkSeg st112 st113 = true := by decide +kernel

theorem seg114 : checkSeg st113 st114 = true := by decide +kernel

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
