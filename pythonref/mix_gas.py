#!/usr/bin/env python3
"""Measure Falcon512ShakeVerifier::verify Sierra gas over the scorer-shaped fixture mix.

Runs the generated `mix_verify_NN` / `mix_base_NN` pairs with `--detailed-resources`,
takes verify - base per fixture, and prints the 8-block, 9-block and overall means. With
the default 11:16 fixture set the overall mean is directly comparable to the
falcon.provably.fast score.

Usage:  python3 pythonref/mix_gas.py [--json out.json]
"""

import argparse
import json
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MIX_JSON = Path(__file__).resolve().parent / "fixtures/mix.json"
PASS_RE = re.compile(r"\[(PASS|FAIL)\]\s+[\w:]*::(mix_(?:verify|base)_\d+)")
SIERRA_RE = re.compile(r"sierra gas:\s*(\d+)")


def run() -> dict[str, int]:
    proc = subprocess.run(
        ["snforge", "test", "-p", "pqbench_falcon_512", "mix_", "--detailed-resources"],
        cwd=REPO, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    gas: dict[str, int] = {}
    cur = None
    for line in out.splitlines():
        m = PASS_RE.search(line)
        if m:
            if m.group(1) == "FAIL":
                raise SystemExit(f"{m.group(2)} FAILED\n{out}")
            cur = m.group(2)
            continue
        ms = SIERRA_RE.search(line)
        if ms and cur:
            gas[cur] = int(ms.group(1))
            cur = None
    if proc.returncode != 0 or not gas:
        raise SystemExit(out)
    return gas


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--json", type=Path, help="also write per-fixture results here")
    args = parser.parse_args()

    fixtures = json.loads(MIX_JSON.read_text())
    gas = run()
    rows = []
    for i, fx in enumerate(fixtures):
        cost = gas[f"mix_verify_{i:02}"] - gas[f"mix_base_{i:02}"]
        rows.append({"fixture": i, "blocks": fx["blocks"], "gas": cost})

    def mean(xs):
        return sum(xs) / len(xs) if xs else float("nan")

    by8 = [r["gas"] for r in rows if r["blocks"] == 8]
    by9 = [r["gas"] for r in rows if r["blocks"] == 9]
    allg = [r["gas"] for r in rows]
    for r in rows:
        print(f"  {r['fixture']:02}  {r['blocks']} blocks  {r['gas']:>12,}")
    print(f"8-block mean ({len(by8)}): {mean(by8):,.0f}   min {min(by8):,} max {max(by8):,}")
    print(f"9-block mean ({len(by9)}): {mean(by9):,.0f}   min {min(by9):,} max {max(by9):,}")
    print(f"mix mean     ({len(allg)}): {mean(allg):,.0f}")
    if args.json:
        args.json.write_text(json.dumps({"rows": rows, "mean": mean(allg),
                                         "mean8": mean(by8), "mean9": mean(by9)}, indent=1))


if __name__ == "__main__":
    main()
