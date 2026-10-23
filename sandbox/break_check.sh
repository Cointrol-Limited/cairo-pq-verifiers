#!/usr/bin/env bash
# Run the Break-track suite against one falcon.provably.fast record, in the sandbox.
#
#   sandbox/break_check.sh JOB_ID
#
# Downloads the record's patch (pvfast, read-only), builds a scratch tree from this working
# tree with crates/*/src reset to the baseline and the patch applied, and runs the
# rare-path (edge_), edge-input (edge_in_), crafted zero-half key (zk_) and mutation (fuzz_)
# vectors offline. Prints
# every verdict that differs from the reference and a one-line summary.
set -euo pipefail

JOB="$1"
REPO="$(cd "$(dirname "$0")/.." && pwd)"
ROOT="$HOME/.cache/falcon-sandbox"
PATCHES="$ROOT/patches"
WORK="$ROOT/work/brk_${JOB:0:11}"
mkdir -p "$PATCHES"
P="$PATCHES/$JOB.patch"
if [ ! -s "$P" ]; then
  (cd "$PATCHES" && uvx --python 3.12 pvfast remote falcon patch "$JOB" --out "$P" >/dev/null)
fi

rm -rf "$WORK" && mkdir -p "$WORK"
(cd "$REPO" && git ls-files -co --exclude-standard -z | xargs -0 tar -cf -) | tar -x -C "$WORK"
mkdir -p "$WORK/crates/falcon_512/tests/data"
cp "$REPO/crates/falcon_512/tests/data/fuzz.txt" "$WORK/crates/falcon_512/tests/data/"
cp "$REPO/crates/falcon_512/tests/bench_fuzz.cairo" "$WORK/crates/falcon_512/tests/"
rm -rf "$WORK/crates/falcon_512/src" "$WORK/crates/ntt/src"
git -C "$REPO" archive bece5c07eeea5784e570c01108ec000d2d04ae40 crates/falcon_512/src crates/ntt/src \
  | tar -x -C "$WORK"
git -C "$WORK" init -q && git -C "$WORK" apply --whitespace=nowarn "$P" && rm -rf "$WORK/.git"
# Only the Break suites are run: drop the other integration tests so the test crate compiles
# within the container's memory (newer records alone take ~6 GB to build with everything).
(cd "$WORK/crates/falcon_512/tests" && rm -f bench_mix.cairo mix_fixtures.cairo bench_blake.cairo \
  bench_poseidon.cairo bench_shake.cairo)

docker run --rm --cap-drop ALL --security-opt no-new-privileges --pids-limit 1024 --memory 6g \
  --network none -v falcon-sandbox-cache:/cache-ro:ro -v "$WORK:/work" falcon-sandbox:1 \
  sh -c 'cp -a /cache-ro/. "$HOME/.cache/" &&
    snforge test -p pqbench_falcon_512 edge_ --max-threads 3 > /work/edge.txt 2>&1;
    snforge test -p pqbench_falcon_512 zk_ --max-threads 3 > /work/zk.txt 2>&1;
    snforge test -p pqbench_falcon_512 fuzz_ --max-threads 2 > /work/fuzz.txt 2>&1;
    echo "edge: $(grep -E "^Tests:" /work/edge.txt | tail -1)";
    grep -E "^\[FAIL\]" /work/edge.txt || true;
    echo "zero-key: $(grep -E "^Tests:" /work/zk.txt | tail -1)";
    grep -E "^\[FAIL\]" -A3 /work/zk.txt || true;
    echo "fuzz: $(grep -E "^Tests:" /work/fuzz.txt | tail -1), $(grep -c "^FUZZ" /work/fuzz.txt) vectors run";
    awk "/^FUZZ/ && \$3!=\$4 {print \"MISMATCH\", \$0}" /work/fuzz.txt;
    grep -E "^\[FAIL\]" -A3 /work/fuzz.txt | grep -v "^--" | head -20 || true'
