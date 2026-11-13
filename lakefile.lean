import Lake
open Lake DSL

package TernaryGoldbach

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

-- Each theorem takes as `Fact` instances only the hypotheses its proof uses; the
-- `unusedSectionVars` linter (on by default) reports a hypothesis a theorem takes but does not use.
@[default_target] lean_lib TernaryGoldbach

-- Helfgott's RSBounds development (Garald1/RSBounds), vendored unchanged under `vendor/rsbounds/`
-- (`source-provenance.json` records the commit and the SHA-256 of every file). It proves
-- [H, (2.21)] (`RamareMoebius`, from `mobius003.tex`) and [H, (2.14)], (2.17) with [H]'s constants.
-- Only the modules that `TernaryGoldbach` imports, and their dependencies, are built. The options of
-- the `rh100` libraries are those of RSBounds' own lakefile.
lean_lib RSBounds where
  srcDir := "vendor/rsbounds"
  globs := #[.submodules `RSBounds]

lean_lib MoebiusCert where
  srcDir := "vendor/rsbounds"
  globs := #[.submodules `MoebiusCert]

lean_lib Zeta23 where
  srcDir := "vendor/rsbounds/rh100"
  globs := #[.submodules `Zeta23]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

lean_lib ZetaLean where
  srcDir := "vendor/rsbounds/rh100"
  globs := #[.submodules `ZetaLean]

lean_lib RHHeight where
  srcDir := "vendor/rsbounds/rh100"
  globs := #[.submodules `RHHeight]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib RHHeight100 where
  srcDir := "vendor/rsbounds/rh100"
  globs := #[.submodules `RHHeight100]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib HardyFirstZero where
  srcDir := "vendor/rsbounds/rh100"
  globs := #[.submodules `HardyFirstZero]

lean_lib HardyTenZeros where
  srcDir := "vendor/rsbounds/rh100"
  globs := #[.submodules `HardyTenZeros]

-- The search for the prime-ladder hints (`LadderHints.lean`) runs during elaboration; compiling it
-- to native code makes it fast. The hints are only a guide: the kernel checks every rung.
lean_lib LadderHints where
  precompileModules := true

-- leanprover/comparator: `Challenge` states the main theorems (with `sorry`), `Solution` proves
-- them. See `comparator/README.md`.
lean_lib Challenge

lean_lib Solution
