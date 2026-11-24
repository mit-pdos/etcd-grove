#!/usr/bin/env bash
# Checks every stream DIR/*.ndjson with TLC (streamcheck.py, MANIFEST default manifest-empty: the
# harness's EtcdBindingEmpty.cfg) and writes DIR/verdicts.txt in verdicts.txt's format (source
# `harness`), for diff_test.go's EXTRA_VERDICTS. Needs what gen-fixtures.sh needs.
#
#   EFR=/path/to/etcd-raft-formalized check/testdata/tlc-dir.sh DIR [MANIFEST]
set -uo pipefail
dir=$(cd "${1:?DIR}" && pwd); m=${2:-manifest-empty}
fm=${EFR:?set EFR}/antithesis-fm
cfg=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["stream_config"])' "$fm/spec/$m.json")
one() {
  f=$1; t=$(mktemp -d); cp "$f" "$t/s.ndjson"; touch "$t/s.ndjson.eof"
  v=$(python3 -I "$fm/tracekit/check/streamcheck.py" "$fm/spec/$m.json" "$t/s.ndjson" 2>&1 | head -1 | cut -c1-300)
  rm -rf "$t"
  echo "harness $(basename "$f") $cfg 0 $v"
}
export -f one; export fm m cfg
ls "$dir"/*.ndjson | xargs -P "${JOBS:-4}" -I{} bash -c 'one {}' > "$dir/verdicts.txt"
awk '{print $5}' "$dir/verdicts.txt" | sort | uniq -c
