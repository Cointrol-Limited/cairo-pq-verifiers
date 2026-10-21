#!/usr/bin/env python3
"""Genuine signatures over edge-valued messages and salts (all-zero, all-one and boundary
lanes of the absorbed SHAKE block), each accepted by the reference verifier. Writes
tests/edge_in_fixtures.cairo + bench_edge_in.cairo via gen_edge_fixtures.write_cairo."""
import itertools
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_edge_fixtures as ge  # noqa: E402

ref = ge.ref
P = ref.FELT_PRIME
M64 = (1 << 64) - 1
msgs = [0, 1, P - 1, (1 << 128) - 1, 1 << 128, (1 << 251) - 1, P - (1 << 128), M64,
        M64 << 64, M64 << 128, (M64 << 192) % P, (1 << 251) - (1 << 128)]
halves = [0, (1 << 160) - 1, (1 << 32) - 1, ((1 << 160) - 1) ^ ((1 << 32) - 1),
          M64, M64 << 64, M64 << 96, 1 << 159]
salts = [(0, 0), ((1 << 160) - 1, (1 << 160) - 1)] + [(a, b) for a, b in zip(halves, reversed(halves))]
scheme = ge.gm.fpy.Falcon(512)
vectors = []
pairs = [(m, s) for m in msgs for s in salts[:2]] + [(msgs[i % len(msgs)], s) for i, s in enumerate(salts[2:])]
for m, (sa, sb) in pairs:
    salt = sa.to_bytes(20, "little") + sb.to_bytes(20, "little")
    fx = ge.sign(scheme, m, salt)
    fx["kind"] = f"msg={hex(m)[:12]} salt=({hex(sa)[:10]},{hex(sb)[:10]})"
    fx["stream"] = ge.stream_state(m, salt)
    vectors.append(fx)
    print(fx["kind"], fx["stream"], flush=True)
ge.write_cairo("edge_in", vectors)
