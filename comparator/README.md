# Checking the main theorems with Comparator

[leanprover/comparator](https://github.com/leanprover/comparator) checks the proof against a
trusted statement:

* `Challenge.lean` (repository root) states the main theorems with `sorry`. Its definitions use
  only Mathlib and are copied from `TernaryGoldbach/Statement.lean`. These are the ternary
  Goldbach statement and the three numerical hypotheses (`PlattGRH`, `BinaryGoldbachInput`,
  `CDEMertens`).
* `Solution.lean` imports `TernaryGoldbach.MainTheorems`, which proves them.
* `config.json` lists the two theorems and permits only `propext`, `Quot.sound` and
  `Classical.choice`.

Comparator checks three things. The declarations in the theorem statements must be the same in
both environments. The proofs must use only the permitted axioms. The kernel must accept the
`Solution` environment when it is replayed.

What you trust: `Challenge.lean`, Mathlib, the lakefile, and the tools (Comparator, lean4export,
landrun, the Lean kernel). The three hypotheses are published numerical results that are not
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

Lake `v4.35.0` also has the check built in:

```sh
lake comparator --config comparator/config.json
```

It builds and exports the project inside a `bwrap` sandbox, so it needs `bubblewrap`, with either
unprivileged user namespaces or a setuid-root `bwrap`.

## Status

On 2026-11-06, at commit `83ac1e1`, `lake comparator --config comparator/config.json` accepted both
theorems:

```
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

The run took 112 minutes, about 90 of them in the kernel replay of `Solution` (single-threaded,
up to about 5 GB). It used `bwrap` 0.9.0 with unprivileged user namespaces, under
`systemd-run --user --scope -p MemoryMax=42G`.

Notes for running it in a container:
* Without a user systemd session, the `systemd-run` wrapper is not available. Run the inner
  `lake env /path/to/comparator comparator/config.json` directly.
* On a kernel that supports only an older Landlock ABI, `landrun` needs `--best-effort`, which is a
  weaker sandbox. `Solution.lean` is the project's own code, so this matters less than it would for
  untrusted input; the kernel check is unaffected.
* Expect the kernel replay of `Solution` to take about an hour and a half.
