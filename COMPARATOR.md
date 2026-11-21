# Running Comparator on a Linux box

Exact commands for checking the main theorems with
[Comparator](https://github.com/leanprover/comparator). Background, what is trusted and the record
of earlier runs are in [`comparator/README.md`](comparator/README.md).

The machine needs about 30 GB of free disk and at least 16 GB of memory (32 GB is safer). More
cores shorten the build, not the kernel replay, which is single-threaded. Expect the whole run to
take a day or more, so use a machine that will stay up.

## 1. Prerequisites

Skip any the machine already has. This assumes Debian or Ubuntu.

```sh
sudo apt-get update && sudo apt-get install -y git curl tmux bubblewrap
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source ~/.elan/env
```

## 2. Sandbox check

This must print `SANDBOX_OK`:

```sh
bwrap --unshare-user --ro-bind / / true && echo SANDBOX_OK
```

If it does not (Ubuntu 24.04 restricts unprivileged user namespaces by default), run this and
repeat the check:

```sh
sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
```

## 3. Get the repository at the commit to check

```sh
git clone https://github.com/calr3/ternary-goldbach
cd ternary-goldbach
git checkout d5bfbaf
```

`d5bfbaf` is the last commit that changed Lean code when this file was written. To check the
latest `main` instead, leave out the `git checkout`. The log records the commit either way.

## 4. Start the run inside `tmux`

```sh
tmux new -s comparator
```

Then, inside the `tmux` session:

```sh
source ~/.elan/env
comparator/run.sh
```

Detach with `Ctrl-b` then `d`. The run continues after you log out.

On a shared machine, cap its memory by starting it with
`systemd-run --user --scope -p MemoryMax=40G comparator/run.sh` instead.

## 5. Check on it later

```sh
tmux attach -t comparator
```

or, without attaching:

```sh
tail -n 20 ~/ternary-goldbach/comparator/logs/run-*.log
```

## What to expect

* The build takes a few hours on 4 cores, less with more.
* The log is then silent for about 80 minutes after `Building Solution`, while `Solution` is
  exported.
* After `Running Lean default kernel on solution` it is silent again for most of a day or more.
  This is the kernel replay.
* Success: the log ends with `Your solution is okay!` and `VERDICT: accepted (exit code 0)`.
* Exit code 1 means a rejection or a failed build inside the sandbox. Exit code 2 means it could
  not start. The log says why.
* If the run is interrupted, run `comparator/run.sh` again. The build is kept, but the export and
  the replay start over.

## What to report

The `commit:` and `machine:` lines at the top of the log, the `real` time, and the log's last 20
lines, so that the run can be recorded in `README.md`, `comparator/README.md` and
`formalization.yaml`.

Lean changes pushed to `main` during the run are not covered by its verdict, which is for the
commit in the log.
