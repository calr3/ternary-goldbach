#!/usr/bin/env bash
# Check the main theorems with Comparator (Lake's built-in `lake comparator`) and keep a log.
# Usage, from anywhere in the repository:   comparator/run.sh
# See "Running it on another machine" in comparator/README.md. Expect it to take about a day; run it
# inside tmux or screen (or under nohup) so that it survives a closed terminal.
set -uo pipefail
cd "$(dirname "$0")/.."

mkdir -p comparator/logs
LOG="comparator/logs/run-$(date -u +%Y%m%dT%H%M%SZ).log"
exec > >(tee -a "$LOG") 2>&1
step() { echo; echo "=== $(date -u +%FT%TZ) $*"; }

step "setup"
echo "log: $LOG"
echo "commit: $(git rev-parse HEAD)$(git diff --quiet HEAD -- . ':!comparator/logs' || echo ' (with local changes)')"
echo "machine: $(nproc) cores, $(free -g | awk '/^Mem:/ {print $2}') GB memory, $(uname -sr)"
lean --version || { echo "lean is not on PATH: install elan (see comparator/README.md)"; exit 2; }
lake --version

step "1. sandbox"
if ! bwrap --unshare-user --ro-bind / / true; then
  echo "bwrap is missing, or cannot create unprivileged user namespaces (see comparator/README.md)"
  exit 2
fi
bwrap --version

step "2. Mathlib's prebuilt files"
lake exe cache get || { echo "lake exe cache get failed"; exit 2; }

step "3. build Challenge and Solution"
# A module can be killed for lack of memory when several heavy ones compile at once (exit code 137,
# e.g. MinorArcs/G2TailNum.lean with 16 GB). Lake keeps what it has built, so the next attempt
# compiles only what is left.
built=0
for attempt in 1 2 3; do
  if lake build Challenge Solution; then built=1; break; fi
  echo "build attempt $attempt failed; retrying"
done
[ "$built" = 1 ] || { echo "the build failed three times; see the errors above"; exit 1; }

step "4. axioms"
AX="$(mktemp --suffix .lean)"
cat > "$AX" <<'EOF'
import TernaryGoldbach.MainTheorems
#print axioms TernaryGoldbach.ternary_goldbach_of_hypotheses
#print axioms TernaryGoldbach.ternary_goldbach_large_of_hypotheses
EOF
lake env lean "$AX"
rm -f "$AX"

step "5. lake comparator --config comparator/config.json"
time lake comparator --config comparator/config.json
status=$?

step "done"
case $status in
  0) echo "VERDICT: accepted (exit code 0)";;
  1) echo "VERDICT: rejected, or the build inside the sandbox failed (exit code 1); see the log";;
  *) echo "VERDICT: could not start (exit code $status); see the log";;
esac
echo "Please send: the commit and machine lines at the top, the 'real' time above, and the last 20 lines of $LOG"
exit $status
