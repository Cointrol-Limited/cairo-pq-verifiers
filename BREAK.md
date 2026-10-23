# Break-track log — Falcon-512 (SHAKE-256) records

Work by Claude (AI agent, Anthropic) under Cointrol's direction, for the
[falcon.provably.fast](https://falcon.provably.fast/) Break track. A break is an input the
record gets wrong against the challenge's reference verifier, or rejects at more than 1.25×
its worst valid gas. Third-party records are built and run only in `sandbox/`.

## Target: record fj_c7ec9408 (24,770,747 gas, odinfree, on fj_dfc79adf)

| Campaign | Vectors | Result |
|---|---|---|
| Rare squeeze paths, genuine signatures (`pythonref/gen_edge_fixtures.py`): 1, 15, 16 coefficients missing after 8 blocks; 17–40 missing (block 9 past lane 3); block 9's first 16 words short of accepts; 8-block finishes with 0, 1, 8 words unused | 24, all valid | All accepted, matching the reference |
| Edge messages and salts, genuine signatures (`gen_edge_inputs.py`): message 0, 1, p−1, 2^128±1, 2^251−1, all-ones lanes; salt halves 0, 2^160−1, 2^32−1, all-ones 64-bit lanes | 32, all valid | All accepted |
| Mutations of genuine signatures (`gen_fuzz.py`): every input felt set to 0, 1, p−1, 2^128±1, ±1, ±2^128, non-canonical re-encodings of the same digits (low/high half + q^9, last slot + q^8); salt-range edges; length ±1; direct-form signature; s1/t swapped | 2,990 (2 valid; HINT 1,948, ENCODING 982, NORM 36, SALT_RANGE 12, LENGTH 10) | Every verdict matches the reference |
| Crafted keys (`gen_zero_keys.py`): genuine keypairs whose packed public key has chosen zero parts — high half of slot 0, 13 or 27, low half of slot 5, all of slot 9 (felt 0), the last slot, high halves of slots 2 and 20 — built by a short correction to g found with LLL + Babai so that NTT(g) vanishes there; two signatures each | 14, all valid | All accepted |

Re-run with `sandbox/break_check.sh` on each later record: fj_eda0c8ca, fj_8b6abcc5,
fj_8dc65143, fj_6b952f5c (24,730,370) — every vector matches the reference on all of them.

**Gas of valid signatures by squeeze path** (local snforge, one verification):
8-block ~23.85M; 9-block via syscall tail ~25.44M; 16+ missing after 8 blocks (Cairo 9th
permutation) ~26.31M; syscall head tried but short of accepts, then the Cairo permutation
anyway ~27.88M. The most expensive reachable path is ~1.08× a normal 9-block signature, so
a slow-reject break would need a further ~4M (about two more permutations), which only a
10-block stream (probability ~1e-18 per salt) could give.

**Reviewed, sound:** `REJECT_NORM` (2^80, added at most 6 times, cannot wrap the felt
below the 34,034,726 bound); hint check by field division (`x/q < 2^128` decides `q | x`
because `0 <= x < 2^137 < p`); the rotated Keccak state (value-dependent branches split
about 50/50, so every signature exercises both sides).

## Tools

- `sandbox/break_check.sh JOB_ID` downloads a record's patch and runs every suite below
  against it offline (about 10 minutes per record).
- `pythonref/gen_zero_keys.py`: genuine keys with chosen all-zero key halves or slots.
- `pythonref/gen_fuzz.py` writes `crates/falcon_512/tests/data/fuzz.txt` (gitignored) and a
  chunked harness that reads it with `snforge_std::fs::read_txt`; run with
  `sandbox/run.sh fz /dev/null snforge test -p pqbench_falcon_512 fuzz_ --max-threads 2`.
- `pythonref/gen_edge_fixtures.py`, `gen_edge_inputs.py`: genuine signatures for chosen
  squeeze states and absorbed-block values, as one test per vector.

## Falcon-1024 season (branch `cointrol/break1024`, on the season baseline bf7fd878)

Judge: `falcon1024.py` (pinned by `pythonref/fetch.sh`). Records are `fk_` jobs. The scored
function is `Falcon1024Verifier::verify` in `crates/falcon_1024`.

| Suite (`pythonref/gen1024.py`) | Vectors | Current record fk_be5fa0d8 (49,357,618) | Nine records before it (fk_11e1961f … fk_3dbc0fd8) |
|---|---|---|---|
| The season's own vectors (`tests/vectors.cairo`, `bench.cairo`) | 12 | Pass | Pass |
| `edge`: genuine signatures over rare squeeze states (k missing after 16 blocks found in block 17's head; 17–40 missing; block 17's head short; 16-block finishes at block ends) and edge messages and salts | 32, all valid | All accepted | All accepted |
| `norm`: genuine signatures walked along the key lattice (s0 + g·x, s1 − f·x) to the bound's edge: 135 below it, 99.6%, 99.1% (valid); +0.03%, +1.07%, +2.0% (invalid) | 6 | All correct | All correct |
| `zk`: crafted keys with zero high halves (slots 0, 30), zero low half (slot 55), an all-zero slot (20), and the last slot's low, high and whole parts zero | 14, all valid | All accepted | All accepted |
| `fuzz`: every felt to edge and non-canonical values, salt edges, lengths, swapped felts, swapped salts, another key, s1 re-hinted to match | 5,912 (2 valid) | Every verdict matches | Not run (about 25 minutes per record) |

Run with `sandbox/break_check1024.sh JOB_ID` (`SKIP_FUZZ=1` for the fast suites). The mutation
run is split into 60 snforge processes run one test at a time, because longer runs exceed the
container's 6 GB.
