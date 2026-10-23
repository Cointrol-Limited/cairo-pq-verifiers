#!/usr/bin/env bash
# Run the Falcon-1024 Break-track suite against one record of that season, in the sandbox.
#
#   sandbox/break_check1024.sh JOB_ID      (fk_... ids)
#
# Downloads the record's patch (pvfast, read-only), builds a scratch tree from this working
# tree (branch cointrol/break1024, on the season baseline bf7fd878) with crates/falcon_1024/src
# and crates/ntt/src reset to the baseline and the patch applied, and runs every
# pqbench_falcon_1024 test offline: the season's own vectors, the rare-path and edge-input
# signatures (e1k_), norm-edge signatures (n1k_), crafted zero-half keys (z1k_) and the
# reference-judged mutations (fuzz1k_; SKIP_FUZZ=1 leaves them out). Prints every failing
# test and verdict mismatch.
set -euo pipefail

JOB="$1"
REPO="$(cd "$(dirname "$0")/.." && pwd)"
BASE=bf7fd8785a189164d638e7f7c11d261c9e864d56
ROOT="$HOME/.cache/falcon-sandbox"
PATCHES="$ROOT/patches1024"
WORK="$ROOT/work/b1k_${JOB:0:11}"
mkdir -p "$PATCHES"
P="$PATCHES/$JOB.patch"
for _ in 1 2 3; do
  [ -s "$P" ] && break
  (cd "$PATCHES" && uvx --python 3.12 pvfast remote falcon1024 patch "$JOB" --out "$P" >/dev/null 2>&1) || sleep 5
done
[ -s "$P" ] || { echo "could not download the patch for $JOB"; exit 1; }

rm -rf "$WORK" && mkdir -p "$WORK"
(cd "$REPO" && git ls-files -co --exclude-standard -z | xargs -0 tar -cf -) | tar -x -C "$WORK"
mkdir -p "$WORK/crates/falcon_1024/tests/data"
cp "$REPO/crates/falcon_1024/tests/data/fuzz.txt" "$WORK/crates/falcon_1024/tests/data/"
cp "$REPO/crates/falcon_1024/tests/bench_fuzz1k.cairo" "$WORK/crates/falcon_1024/tests/"
rm -rf "$WORK/crates/falcon_1024/src" "$WORK/crates/ntt/src"
git -C "$REPO" archive "$BASE" crates/falcon_1024/src crates/ntt/src | tar -x -C "$WORK"
git -C "$WORK" init -q && git -C "$WORK" apply --whitespace=nowarn "$P" && rm -rf "$WORK/.git"

docker run --rm --cap-drop ALL --security-opt no-new-privileges --pids-limit 1024 --memory 6g \
  --network none -e SKIP_FUZZ="${SKIP_FUZZ:-0}" -v falcon-sandbox-cache:/cache-ro:ro -v "$WORK:/work" falcon-sandbox:1 \
  sh -c 'cp -a /cache-ro/. "$HOME/.cache/" &&
    if [ "$SKIP_FUZZ" = 1 ]; then rm -f crates/falcon_1024/tests/bench_fuzz1k.cairo; fi;
    snforge test -p pqbench_falcon_1024 --skip fuzz1k_ --max-threads 2 --max-n-steps 200000000 > /work/all.txt 2>&1;
    if [ "$SKIP_FUZZ" != 1 ]; then
      for p in $(seq -f "%03g" 0 59); do
        snforge test -p pqbench_falcon_1024 fuzz1k_$p --max-threads 1 --max-n-steps 200000000 >> /work/all.txt 2>&1;
      done;
    fi;
    grep -E "^Tests:" /work/all.txt | awk "{p+=\$2; f+=\$4} END {print \"tests: \" p \" passed, \" f \" failed\"}";
    echo "fuzz vectors run: $(grep -c "^FUZZ" /work/all.txt)";
    grep -E "^\[FAIL\]" /work/all.txt | head -20 || true;
    awk "/^FUZZ/ && \$3!=\$4 {print \"MISMATCH\", \$0}" /work/all.txt;
    grep -E "Failed to build|error\[" /work/all.txt | head -5 || true'
