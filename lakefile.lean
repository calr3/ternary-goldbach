import Lake
open Lake DSL

package TernaryGoldbach

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

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
