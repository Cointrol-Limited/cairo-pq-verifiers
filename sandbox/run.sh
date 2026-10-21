#!/usr/bin/env bash
# Build and test a third-party patch inside the falcon-sandbox container.
#
#   sandbox/run.sh --image                 build the falcon-sandbox image
#   sandbox/run.sh --warm                  fill the dependency cache volume (network on)
#   sandbox/run.sh NAME PATCH [CMD...]     copy HEAD of this repo to a scratch tree,
#                                          `git apply` PATCH, run CMD offline (default:
#                                          the mix gas benchmark)
#
# Scratch trees live in ~/.cache/falcon-sandbox/work/NAME (Colima only shares $HOME with
# its VM). Containers run as an unprivileged user with no network and no capabilities,
# on a private copy of the read-only dependency cache.
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
IMAGE=falcon-sandbox:1
CACHE_VOL=falcon-sandbox-cache
ROOT="$HOME/.cache/falcon-sandbox"

harden=(--rm --cap-drop ALL --security-opt no-new-privileges --pids-limit 1024 --memory 6g)

tree_from_head() {  # $1 = destination
  rm -rf "$1" && mkdir -p "$1"
  git -C "$REPO" archive HEAD | tar -x -C "$1"
}

case "${1:-}" in
  --image)
    ctx="$ROOT/image-ctx"; rm -rf "$ctx"; mkdir -p "$ctx"
    cp "$REPO/sandbox/Dockerfile" "$ctx/"
    docker build -q -t "$IMAGE" "$ctx"
    ;;
  --warm)
    tree_from_head "$ROOT/warm"
    docker run "${harden[@]}" -v "$CACHE_VOL:/home/runner/.cache" -v "$ROOT/warm:/work" \
      "$IMAGE" sh -c 'scarb build && snforge test -p pqbench_falcon_512 mix_base_00'
    ;;
  ""|-h|--help)
    sed -n '2,13p' "$0"; exit 1
    ;;
  *)
    name="$1"; patch="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"; shift 2
    work="$ROOT/work/$name"
    tree_from_head "$work"
    git -C "$work" init -q
    if [ -s "$patch" ]; then git -C "$work" apply --whitespace=nowarn "$patch"; fi
    rm -rf "$work/.git"
    if [ $# -eq 0 ]; then set -- python3 pythonref/mix_gas.py; fi
    docker run "${harden[@]}" --network none \
      -v "$CACHE_VOL:/cache-ro:ro" -v "$work:/work" "$IMAGE" \
      sh -c 'cp -a /cache-ro/. "$HOME/.cache/" && exec "$@"' sh "$@"
    ;;
esac
