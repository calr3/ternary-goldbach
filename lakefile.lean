import Lake
open Lake DSL

package TernaryGoldbach

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

-- Helfgott's RSBounds (Garald1/RSBounds), pinned to the commit checked so far. It proves [H, (2.21)]
-- (`RamareMoebius`, from `mobius003.tex`) and [H, (2.14)], (2.17) with [H]'s constants. RSBounds in
-- turn requires this repository (as `TernaryGoldbach`, at `192ca57`). Lake resolves that requirement
-- to this package instead of fetching the older commit, so RSBounds is compiled against the current
-- modules. Only the RSBounds modules that `TernaryGoldbach` imports, and their dependencies, are built.
require RSBounds from git "https://github.com/Garald1/RSBounds" @
  "0393b52234b29baf18fbfd02a60a2fca341a5c64"

-- Each theorem takes as `Fact` instances only the hypotheses its proof uses; the
-- `unusedSectionVars` linter (on by default) reports a hypothesis a theorem takes but does not use.
@[default_target] lean_lib TernaryGoldbach

-- The search for the prime-ladder hints (`LadderHints.lean`) runs during elaboration; compiling it
-- to native code makes it fast. The hints are only a guide: the kernel checks every rung.
lean_lib LadderHints where
  precompileModules := true

-- leanprover/comparator: `Challenge` states the main theorems (with `sorry`), `Solution` proves
-- them. See `comparator/README.md`.
lean_lib Challenge

lean_lib Solution
