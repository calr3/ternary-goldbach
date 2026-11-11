/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/

import RSBounds.LambdaCert.States

/-!
# Kernel checks of segments 77–95 (`n` from 188416 to 262144)
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

theorem seg77 : checkSeg st76 st77 = true := by decide +kernel

theorem seg78 : checkSeg st77 st78 = true := by decide +kernel

theorem seg79 : checkSeg st78 st79 = true := by decide +kernel

theorem seg80 : checkSeg st79 st80 = true := by decide +kernel

theorem seg81 : checkSeg st80 st81 = true := by decide +kernel

theorem seg82 : checkSeg st81 st82 = true := by decide +kernel

theorem seg83 : checkSeg st82 st83 = true := by decide +kernel

theorem seg84 : checkSeg st83 st84 = true := by decide +kernel

theorem seg85 : checkSeg st84 st85 = true := by decide +kernel

theorem seg86 : checkSeg st85 st86 = true := by decide +kernel

theorem seg87 : checkSeg st86 st87 = true := by decide +kernel

theorem seg88 : checkSeg st87 st88 = true := by decide +kernel

theorem seg89 : checkSeg st88 st89 = true := by decide +kernel

theorem seg90 : checkSeg st89 st90 = true := by decide +kernel

theorem seg91 : checkSeg st90 st91 = true := by decide +kernel

theorem seg92 : checkSeg st91 st92 = true := by decide +kernel

theorem seg93 : checkSeg st92 st93 = true := by decide +kernel

theorem seg94 : checkSeg st93 st94 = true := by decide +kernel

theorem seg95 : checkSeg st94 st95 = true := by decide +kernel

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
