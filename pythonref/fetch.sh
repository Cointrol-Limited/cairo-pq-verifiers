#!/usr/bin/env bash
# Fetch the pinned third-party Python references into pythonref/vendor/ (gitignored)
# and create the pythonref/.venv environment they run in.
#
#   vendor/falcon512.py  the falcon.provably.fast reference verifier (the evaluator's oracle)
#   vendor/falcon1024.py the Falcon-1024 season's reference verifier
#   vendor/falcon.py/    github.com/tprest/falcon.py, for keygen and signing
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
VENDOR="$HERE/vendor"
REF_URL="https://falcon.provably.fast/reference/falcon512.py"
REF_SHA256="54624238ace29aafef1283f56edfae7ab9d9dded063986850d50b48d7ce713e2"
REF1024_URL="https://postquantum.provably.fast/reference/falcon1024.py"
REF1024_SHA256="0d344416723fb0e0ed90d0bcf70655f042a556a8173ec71c83de3edd7bd51fe4"
FALCON_PY_URL="https://github.com/tprest/falcon.py"
FALCON_PY_COMMIT="5145a818c9512b4a443507d3375e75dae3076af6"

mkdir -p "$VENDOR"

if [ ! -f "$VENDOR/falcon512.py" ]; then
  curl -fsSL "$REF_URL" -o "$VENDOR/falcon512.py.tmp"
  mv "$VENDOR/falcon512.py.tmp" "$VENDOR/falcon512.py"
fi
echo "$REF_SHA256  $VENDOR/falcon512.py" | shasum -a 256 -c - \
  || { echo "reference verifier changed upstream; review it before re-pinning" >&2; exit 1; }

if [ ! -f "$VENDOR/falcon1024.py" ]; then
  curl -fsSL "$REF1024_URL" -o "$VENDOR/falcon1024.py.tmp"
  mv "$VENDOR/falcon1024.py.tmp" "$VENDOR/falcon1024.py"
fi
echo "$REF1024_SHA256  $VENDOR/falcon1024.py" | shasum -a 256 -c - \
  || { echo "Falcon-1024 reference changed upstream; review it before re-pinning" >&2; exit 1; }

if [ ! -d "$VENDOR/falcon.py/.git" ]; then
  git clone -q "$FALCON_PY_URL" "$VENDOR/falcon.py"
fi
git -C "$VENDOR/falcon.py" -c advice.detachedHead=false checkout -q "$FALCON_PY_COMMIT"

if [ ! -x "$HERE/.venv/bin/python" ]; then
  uv venv -q --python 3.12 "$HERE/.venv"
fi
uv pip install -q --python "$HERE/.venv/bin/python" -r "$HERE/requirements.txt"
echo "pythonref ready: $HERE/.venv/bin/python"
