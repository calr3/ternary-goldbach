import Lake
open Lake DSL

package TernaryGoldbach

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

@[default_target] lean_lib TernaryGoldbach where
  -- the hypotheses are section variables (`variable [Fact …]`), included in every theorem
  leanOptions := #[⟨`linter.unusedSectionVars, false⟩]

-- leanprover/comparator: `Challenge` states the main theorems (with `sorry`), `Solution` proves
-- them. See `comparator/README.md`.
lean_lib Challenge

lean_lib Solution
