# Checking the main theorems with Comparator

[leanprover/comparator](https://github.com/leanprover/comparator) checks the proof against a
trusted statement:

* `Challenge.lean` (repository root) states the main theorems with `sorry`. Its definitions use
  only Mathlib and are copied from `TernaryGoldbach/Statement.lean`. These are the ternary
  Goldbach statement and the four numerical hypotheses (`RHUpTo`, `PlattGRH`,
  `BinaryGoldbachInput`, `RamareMoebius`).
* `Solution.lean` imports `TernaryGoldbach.MainTheorems`, which proves them.
* `config.json` lists the two theorems and permits only `propext`, `Quot.sound` and
  `Classical.choice`.

Comparator checks three things. The declarations in the theorem statements must be the same in
both environments. The proofs must use only the permitted axioms. The kernel must accept the
`Solution` environment when it is replayed.

What you trust: `Challenge.lean`, Mathlib, the lakefile, and the tools (Comparator, lean4export,
landrun, the Lean kernel). The four hypotheses are published numerical results that are not
formalized. They appear as explicit hypotheses of the theorems, so you also need to check that
they say what the cited papers prove (see `HYPOTHESES.md`).

## Running it

You need `landrun` (built from its `main` branch) and a `lean4export` that matches Lean `v4.35.0`
in `PATH`, plus a Comparator build. Then, from the repository root:

```sh
lake build
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- bash -c 'lake env /path/to/comparator comparator/config.json'
```

(The `systemd-run` wrapper guards against a known landrun weakness. See Comparator's README.)

## Last run

On 2026-11-04, at commit `3efc51f`, the run took 69 minutes on 4 cores and ended with:

```
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

That container had no user systemd session, so the run skipped the `systemd-run` wrapper. Its
kernel supports Landlock ABI v7 only, so `landrun` ran with `--best-effort`, which is a weaker
sandbox. `Solution.lean` is our own code, so a weaker sandbox mattered less than it would for
untrusted input. The kernel check is unaffected.

On 2026-11-05, on branch `platt-grh-rh` at commit `4c2186d` (RH to 3·10¹⁰, binary Goldbach to
4·10¹⁸, `ButhePsi` up to 10¹⁷; `ButhePsi` has since been removed), the same setup took 97 minutes
and ended with:

```
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Comparator has not yet been run on the four-hypothesis statements (branch `buthe-free`).
