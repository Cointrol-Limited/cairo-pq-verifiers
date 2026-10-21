#!/usr/bin/env bash
# Size gates for the working tree, as the falcon.provably.fast scorer applies them:
#   patch bytes  `git diff --full-index` of crates/falcon_512/src and crates/ntt/src
#                against the baseline (fixtures excluded), cap 262,144
#   class bytes  pq_accounts_Falcon512ShakeAccount.contract_class.json built with the
#                audited libfunc list, cap 4,089,446 (Starknet's contract class limit)
# The build runs in the sandbox (sandbox/run.sh).
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
BASE=bece5c07eeea5784e570c01108ec000d2d04ae40

patch_bytes=$(git -C "$REPO" diff --full-index "$BASE" -- crates/falcon_512/src crates/ntt/src \
  ':(exclude)crates/falcon_512/src/fixtures' ':(exclude)crates/falcon_512/src/fixtures.cairo' | wc -c)
untracked=$(git -C "$REPO" ls-files -o --exclude-standard -- crates/falcon_512/src crates/ntt/src)
[ -n "$untracked" ] && echo "note: untracked files not counted: $untracked"
printf 'patch bytes  %8d / 262144  (headroom %d)\n' "$patch_bytes" $((262144 - patch_bytes))

"$REPO/sandbox/run.sh" check /dev/null sh -c '
  sed -i "s/allowed-libfuncs-list.name = \"experimental\"/allowed-libfuncs-list.name = \"audited\"/" pq-accounts/contracts/Scarb.toml
  scarb build -p pq_accounts 2>&1 | grep -E "^error|not allowed" | grep -i shakeaccount || true
  f=target/dev/pq_accounts_Falcon512ShakeAccount.contract_class.json
  b=$(wc -c < $f)
  printf "class bytes  %8d / 4089446  (headroom %d)\n" $b $((4089446 - b))'
