#!/usr/bin/env bash
# Build spec modules on the specs-only branch, serialized: several agents share one worktree and
# one .lake, so every `lake build` goes through this lock. Usage:
#   etc/specs-build.sh Spec.go_etcd_io.etcd.client.v3.Api Spec.go_etcd_io.etcd.client.v3.kv__Put
#   etc/specs-build.sh --dir Spec/go_etcd_io/etcd/client/v3     # every module directly in DIR
set -euo pipefail
cd "$(dirname "$0")/.."
mods=()
if [ "${1:-}" = "--dir" ]; then
  shift
  for d in "$@"; do
    while IFS= read -r f; do m=${f%.lean}; mods+=("${m//\//.}"); done \
      < <(find "$d" -maxdepth 1 -name '*.lean' | sort)
  done
else
  mods=("$@")
fi
[ ${#mods[@]} -gt 0 ] || { echo "specs-build: no modules"; exit 2; }
exec 9>.lake/specs-build.lock
flock 9
lake build "${mods[@]}" 2>&1 | grep -vE '^(✔|⣿|info: )' | grep -v 'Replayed' || true
if lake build --no-build "${mods[@]}" >/dev/null 2>&1; then
  echo "specs-build: OK (${#mods[@]} modules)"
else
  echo "specs-build: FAILED"; exit 1
fi
