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
| Challenge record (2026-10-21) | 26,540,952 | by others; always measure against the latest |

## Log

| Date | Commit | Change | `bench_verify_falcon_512_shake` (9-block) | 11:16 mix mean | Δ vs prev |
|---|---|---|---|---|---|
| 2026-10-21 | `bece5c0` | Baseline, unmodified | 50,190,408 | — (8-block fixtures not yet generated) | — |

Other baseline numbers from the same run:
`bench_verify_falcon_512_shake_direct` 60,439,238;
`bench_validate_falcon_512_shake` (account `__validate__`) 68,022,648.
