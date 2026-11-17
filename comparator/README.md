# Checking the main theorems with Comparator

[leanprover/comparator](https://github.com/leanprover/comparator) checks the proof against a
trusted statement:

* `Challenge.lean` (repository root) states the main theorems with `sorry`. Its definitions use
  only Mathlib and are copied from `TernaryGoldbach/Statement.lean`. These are the ternary
  Goldbach statement and the two numerical hypotheses (`PlattGRH`, `BinaryGoldbachInput`).
* `Solution.lean` imports `TernaryGoldbach.MainTheorems`, which proves them.
* `config.json` lists the two theorems and permits only `propext`, `Quot.sound` and
  `Classical.choice`.

Comparator checks three things. The declarations in the theorem statements must be the same in
both environments. The proofs must use only the permitted axioms. The kernel must accept the
`Solution` environment when it is replayed.

What you trust: `Challenge.lean`, Mathlib, the lakefile, and the tools (Comparator, lean4export,
landrun, the Lean kernel). The two hypotheses are published numerical results that are not
formalized. They appear as explicit hypotheses of the theorems, so you also need to check that
they say what the cited papers prove (see `HYPOTHESES.md`).

## Running it on another machine

The check takes about a day (RSBounds' run of the same statements took 22 h 56 min), almost all of
it in a single-threaded kernel replay, so run it on a machine that will stay up.
`comparator/run.sh` does everything below the setup and keeps a timestamped log in
`comparator/logs/`.

**What the machine needs**
* Linux with `git` and `curl`, and network access to GitHub and Mathlib's cache.
* Memory: at least 16 GB, preferably 32 GB. The build compiles several modules at once (with 16 GB
  and 4 at a time, `MinorArcs/G2TailNum.lean` was once killed for lack of memory). Exporting
  `Solution` took about 8 GB in a test run, and the kernel replay has peaked around 5 GB.
* Cores: more cores shorten the build (a few hours on 4 cores), not the replay.
* Disk: about 30 GB free (the build is about 15 GB, and the exports need room too).
* `bubblewrap`, with unprivileged user namespaces or installed setuid root. This must succeed:
  `bwrap --unshare-user --ro-bind / / true`.

**Setup** (once):

```sh
# Lean: elan installs the version in lean-toolchain (v4.35.0) on first use
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source ~/.elan/env
# bubblewrap, e.g. on Debian or Ubuntu
sudo apt-get install -y bubblewrap
# the repository, at the commit to check
git clone https://github.com/calr3/ternary-goldbach
cd ternary-goldbach
git checkout main        # or a specific commit; the script records which
```

**Run** (inside `tmux` or `screen`, so that it survives a closed terminal):

```sh
tmux new -s comparator
comparator/run.sh
```

On a shared machine, cap its memory with
`systemd-run --user --scope -p MemoryMax=40G comparator/run.sh`.

The script:
1. checks that `bwrap` can create a user namespace;
2. downloads Mathlib's prebuilt files (`lake exe cache get`); Lake fetches the other dependencies,
   RSBounds among them, at the commits in `lake-manifest.json`;
3. builds `Challenge` and `Solution` (`lake build Challenge Solution`), retrying up to three times,
   since a module killed for lack of memory is simply compiled again;
4. prints the axioms of both main theorems, which should be only `propext`, `Classical.choice` and
   `Quot.sound`;
5. runs `lake comparator --config comparator/config.json`. Inside the sandbox it resolves the
   dependencies, rebuilds (nothing is left to compile after step 3), exports `Challenge` and
   `Solution`, and replays `Solution` in Lean's kernel.

The log is quiet for long stretches. In a test run here (4 cores, 15 GB, with everything already
built), steps 1–4 took 20 seconds; after `Building Solution` the export of `Solution` ran for about
80 minutes with no output (one process at full CPU) before `Running Lean default kernel on solution`
started the replay, which is the part that takes about a day.

**Success** looks like this at the end of the log:

```
Lean default kernel accepts the solution
Your solution is okay!
...
VERDICT: accepted (exit code 0)
```

Exit code 1 means a rejection or a failed build inside the sandbox; 2 means it could not start
(`bwrap`, the manifest or the configuration). Either way the log says why. If the run is
interrupted, start `comparator/run.sh` again: the build is kept, but the export and the replay start
over.

**Please report** the `commit:` and `machine:` lines at the top of the log, the `real` time, and the
log's last 20 lines, so that this file, the README and `formalization.yaml` can record the run.

### With the standalone Comparator

Comparator also exists as a separate tool. That needs `landrun` (built from its `main` branch), a
`lean4export` that matches Lean `v4.35.0` in `PATH`, and a Comparator build. Then, from the
repository root:

```sh
lake build Challenge Solution
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- bash -c 'lake env /path/to/comparator comparator/config.json'
```

(The `systemd-run` wrapper guards against a known landrun weakness. See Comparator's README.)

## Status

**The proof on `main` has not been through Comparator yet.** `Challenge.lean` and `config.json`
state the two-hypothesis theorems (`PlattGRH`, `BinaryGoldbachInput`), and no completed run of
`Solution` has been recorded for them. An attempt on 2026-11-14, at commit `8f8d4c2`, in a
container with 4 cores and 15 GB of memory, got through building and exporting `Challenge` and
`Solution`. Its kernel replay of `Solution` then ran for 11.5 hours (single-threaded, about 3.7 GB)
without finishing, and the container restarted before it gave a verdict.

The same two statements have passed Comparator with another proof. Helfgott reported on Zulip
(2026-11-16) that RSBounds' [Comparator configuration](https://github.com/Garald1/RSBounds/blob/ec35ed41b034506e303b2ba90cf18963d6265403/comparator-ternary-goldbach.json),
which checks `RSBounds.Moebius003.UpstreamMain` against RSBounds'
[challenge file](https://github.com/Garald1/RSBounds/blob/ec35ed41b034506e303b2ba90cf18963d6265403/comparator/TernaryGoldbachChallenge.lean), passed in 22 h 56 min. That challenge file has the same definitions and the same two theorem
statements as `Challenge.lean` (as `ternary_goldbach_of_two_hypotheses` and
`ternary_goldbach_large_of_plattGRH`), plus `ramareMoebius_of_plattGRH`. Its proof is RSBounds'
assembly, built on this repository at `192ca57`.

The only recorded run is of an earlier version. On 2026-11-06, at commit `83ac1e1`, the main
theorems took four hypotheses (`RHUpTo`, `PlattGRH`, `BinaryGoldbachInput`, `RamareMoebius`), and
`lake comparator --config comparator/config.json` accepted both theorems:

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
* Expect the kernel replay of `Solution` to take about a day (see above; RSBounds' run of the same
  statements took 22 h 56 min): it re-checks RSBounds' certificates and the prime ladder. Use a
  machine that will not be interrupted.
