/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/

import RSBounds.LambdaCert.States

/-!
# Kernel checks of segments 286–292 (`n` from 1019904 to 1048576)
-/

namespace TernaryGoldbach.RSBounds.LambdaInputs.Cert

theorem seg286 : checkSeg st285 st286 = true := by decide +kernel

theorem seg287 : checkSeg st286 st287 = true := by decide +kernel

theorem seg288 : checkSeg st287 st288 = true := by decide +kernel

theorem seg289 : checkSeg st288 st289 = true := by decide +kernel

theorem seg290 : checkSeg st289 st290 = true := by decide +kernel

theorem seg291 : checkSeg st290 st291 = true := by decide +kernel

theorem seg292 : checkSeg st291 st292 = true := by decide +kernel

end TernaryGoldbach.RSBounds.LambdaInputs.Cert
