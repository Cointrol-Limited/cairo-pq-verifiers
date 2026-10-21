#!/usr/bin/env bash
# Check every new falcon.provably.fast record with the Break-track suite.
#
# Run by launchd (sandbox/com.cointrol.falcon-watch.plist) every two hours, or by hand.
# Reads the leaderboard, runs sandbox/break_check.sh on each record not yet in
# ~/.cache/falcon-sandbox/watch/checked.txt, appends results to watch.log, and posts a
# macOS notification when a verdict differs from the reference or a check fails to run.
# Nothing is ever submitted: an attack job needs the owner's explicit approval.
set -uo pipefail
export PATH="/opt/homebrew/bin:$HOME/.local/bin:$PATH"

REPO="$(cd "$(dirname "$0")/.." && pwd)"
W="$HOME/.cache/falcon-sandbox/watch"
TREE="$W/tree"
LOG="$W/watch.log"
DONE="$W/checked.txt"
mkdir -p "$W" && touch "$DONE"
exec >>"$LOG" 2>&1
echo "=== $(date '+%Y-%m-%d %H:%M:%S') start"

notify() {
  osascript -e "display notification \"$1\" with title \"Falcon break watch\"" || true
}

# Dedicated worktree on cointrol/break, so the user's checkout can be on any branch.
if [ ! -d "$TREE/.git" ] && [ ! -f "$TREE/.git" ]; then
  git -C "$REPO" worktree add --force "$TREE" cointrol/break || { notify "worktree setup failed"; exit 1; }
fi
git -C "$TREE" checkout -q cointrol/break && git -C "$TREE" pull -q --ff-only 2>/dev/null || true
mkdir -p "$TREE/pythonref" && ln -sfn "$REPO/pythonref/vendor" "$TREE/pythonref/vendor"
if [ ! -s "$TREE/crates/falcon_512/tests/data/fuzz.txt" ]; then
  (cd "$TREE" && "$REPO/pythonref/.venv/bin/python" pythonref/gen_fuzz.py --bases 2 --chunk 30) \
    || { notify "fuzz vector generation failed"; exit 1; }
fi

colima status >/dev/null 2>&1 || colima start || { notify "colima would not start"; exit 1; }

ids=$(cd "$W" && uvx --python 3.12 pvfast remote falcon results --format human 2>&1 \
  | grep -oE 'fj_[0-9a-f]{32}' | awk '!seen[$0]++')
[ -z "$ids" ] && { echo "no leaderboard (offline?)"; exit 0; }
record=$(cd "$W" && uvx --python 3.12 pvfast remote falcon results --format human 2>&1 \
  | sed -n 's/^Record: .*\(fj_[0-9a-f]\{32\}\).*/\1/p')

for id in $ids; do
  grep -qx "$id" "$DONE" && continue
  echo "--- $id"
  out=$("$TREE/sandbox/break_check.sh" "$id" 2>&1 | grep -v '^warn\|^ -->')
  echo "$out"
  if echo "$out" | grep -q "MISMATCH\|\[FAIL\]"; then
    notify "Possible break in $id: verdict differs from the reference. See $LOG"
  elif echo "$out" | grep -q "fuzz: Tests: 100 passed, 0 failed" \
      && echo "$out" | grep -q "edge: Tests: [0-9]* passed, 0 failed" \
      && echo "$out" | grep -q "zero-key: Tests: [0-9]* passed, 0 failed"; then
    echo "$id" >>"$DONE"
  else
    notify "Check of $id did not complete. See $LOG"
  fi
done
echo "=== $(date '+%Y-%m-%d %H:%M:%S') done (record ${record:-?})"
