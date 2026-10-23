#!/usr/bin/env bash
# Check every new falcon.provably.fast record with the Break-track suite.
#
# Runs from its own clone of the public repository (launchd cannot read ~/Documents):
#   git clone -b cointrol/break https://github.com/Cointrol-Limited/cairo-pq-verifiers \
#     ~/.cache/falcon-sandbox/watch/repo
# and is started every two hours by sandbox/com.cointrol.falcon-watch.plist. Each run
# fast-forwards the clone, reads the leaderboard, runs sandbox/break_check.sh on each record
# not yet in ~/.cache/falcon-sandbox/watch/checked.txt, appends results to watch.log, and
# posts a macOS notification when a verdict differs from the reference or a check fails.
# Nothing is ever submitted: an attack job needs the owner's explicit approval.
set -uo pipefail
export PATH="/opt/homebrew/bin:$HOME/.local/bin:/usr/bin:/bin:/usr/sbin:/sbin"

REPO="$(cd "$(dirname "$0")/.." && pwd)"
W="$HOME/.cache/falcon-sandbox/watch"
LOG="$W/watch.log"
DONE="$W/checked.txt"
mkdir -p "$W" && touch "$DONE"
exec >>"$LOG" 2>&1
echo "=== $(date '+%Y-%m-%d %H:%M:%S') start"

notify() {
  osascript -e "display notification \"$1\" with title \"Falcon break watch\"" || true
}

git -C "$REPO" pull -q --ff-only || echo "pull failed; using the current checkout"
[ -x "$REPO/pythonref/.venv/bin/python" ] && [ -f "$REPO/pythonref/vendor/falcon512.py" ] \
  || "$REPO/pythonref/fetch.sh" || { notify "pythonref setup failed"; exit 1; }
if [ ! -s "$REPO/crates/falcon_512/tests/data/fuzz.txt" ]; then
  (cd "$REPO" && pythonref/.venv/bin/python pythonref/gen_fuzz.py --bases 2 --chunk 30) \
    || { notify "fuzz vector generation failed"; exit 1; }
fi

colima status >/dev/null 2>&1 || colima start || { notify "colima would not start"; exit 1; }

board=$(cd "$W" && uvx --python 3.12 pvfast remote falcon results --format human 2>&1)
ids=$(echo "$board" | grep -oE 'fj_[0-9a-f]{32}' | awk '!seen[$0]++')
[ -z "$ids" ] && { echo "no leaderboard (offline?)"; exit 0; }
record=$(echo "$board" | sed -n 's/^Record: .*\(fj_[0-9a-f]\{32\}\).*/\1/p')

for id in $ids; do
  grep -qx "$id" "$DONE" && continue
  echo "--- $id"
  out=$("$REPO/sandbox/break_check.sh" "$id" 2>&1 | grep -v '^warn\|^ -->')
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
