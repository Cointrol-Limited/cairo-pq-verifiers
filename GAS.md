# Gas log — Falcon-512 (SHAKE-256) verifier

Work by Claude (AI agent, Anthropic) under Cointrol's direction, for the
[falcon.provably.fast](https://falcon.provably.fast/) Cheaper track.
Baseline: OpenZeppelin `cairo-pq-verifiers` @ `bece5c07eeea5784e570c01108ec000d2d04ae40`.

Toolchain: Scarb 2.18.0, Starknet Foundry 0.59.0 (see `.tool-versions`).
Gas figures are snforge `l2_gas` (Sierra gas) unless noted.

## Reference points

| Source | Gas | Notes |
|---|---|---|
| Challenge baseline (published) | 48,398,466 | mean over 11×8-block + 16×9-block |
| Challenge record (2026-10-21, morning) | 26,540,952 | by others |
| Challenge record `fj_8777d5b7` (2026-10-21, afternoon) | 25,078,934 | by others; patch 260,646 B of the 262,144 B cap |

## Log

| Date | Commit | Change | `bench_verify_falcon_512_shake` (9-block) | 11:16 mix mean | Δ vs prev |
|---|---|---|---|---|---|
| 2026-10-21 | `bece5c0` | Baseline, unmodified | 50,190,408 | 48,393,519 (8: 45,818,918 · 9: 50,163,557) | — |

| 2026-10-21 | record `fj_8777d5b7` on `bece5c0` (sandbox) | Third-party record, unmodified | — | 25,076,712 (8: 24,126,343 · 9: 25,730,091) | — |

Record `fj_8777d5b7`, 9-block fixture 11 (cairo-steps run): 158,374 steps (62% of gas),
10,879 bitwise (25%), 32,363 range checks (9%), 9 keccak-syscall rounds (5%). Profile:
Keccak-f permutation 75%, NTT/unpack/hint+norm 17%, squeeze glue 6%.

Other baseline numbers from the same run:
`bench_verify_falcon_512_shake_direct` 60,439,238;
`bench_validate_falcon_512_shake` (account `__validate__`) 68,022,648.

## Measuring

`pythonref/mix_gas.py` measures `verify` (paired verify − base) over 27 local fixtures in
the scorer's 11:16 mix of 8- and 9-block signatures (`pythonref/gen_mix_fixtures.py`).
On the baseline it reads about 4.9k gas *below* the published per-class means, a
near-constant offset, so compare deltas, not absolute values. Within a block class the
spread is about ±12k gas.
