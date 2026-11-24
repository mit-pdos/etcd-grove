#!/usr/bin/env bash
# Records TLC's verdicts on Antithesis's report streams, for the differential test (diff_test.go),
# which then runs without Java. Needs a checkout of antithesishq/etcd-raft-formalized at the commit
# third_party/etcd-raft-formalized/README.md names, set up by its scripts/setup.sh (tla2tools.jar,
# the compiled TraceKit stream operator), java and python3 on PATH, and go (for the simulator).
#
#   EFR=/path/to/etcd-raft-formalized testdata/gen-fixtures.sh [SEEDS]     (default 12 seeds a mode)
#   OUT=DIR SIMONLY=1 MODES=more EFR=... testdata/gen-fixtures.sh 60    a larger simulator batch, in DIR
#                                 (for diff_test.go's EXTRA_VERDICTS=DIR/verdicts.txt; not committed)
#
# Writes, under testdata/:
#   traces/<name>.ndjson.gz       Antithesis's recorded streams (antithesis-fm/traces/<name>)
#   mutations/<name>.ndjson.gz    each mutation of antithesis-fm/scripts/mutate.py applied as
#                                 scripts/validator-tests.sh does, cut after the event TLC stops at
#   sim/<mode>-<seed>.ndjson.gz   simulator streams (antithesis-fm/sim), as scripts/sim-batch.sh runs it
#   verdicts.txt                  one line per stream: source, file, binding config, changed index
#                                 (mutations; else 0), and streamcheck.py's verdict line
set -uo pipefail
here=${OUT:-$(cd "$(dirname "$0")" && pwd)}
mkdir -p "$here"; here=$(cd "$here" && pwd)
fm=${EFR:?set EFR to the etcd-raft-formalized checkout}/antithesis-fm
seeds=${1:-12}
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
rm -rf "$here/traces" "$here/mutations" "$here/sim"
mkdir -p "$here/traces" "$here/mutations" "$here/sim"
out="$here/verdicts.txt"
: > "$out"

manifest() { # trace directory name -> manifest (as validator-tests.sh)
  local m=manifest
  case "$1" in m-*) m=${m}-m ;; *5*) m=${m}5 ;; esac
  case "$1" in *-empty) m=$m-empty ;; esac
  echo "$m"
}
cfgof() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["stream_config"])' "$fm/spec/$1.json"; }
verdict() { # stream manifest -> streamcheck.py's line
  cp "$1" "$tmp/s.ndjson"; rm -f "$tmp"/s.ndjson.*; touch "$tmp/s.ndjson.eof"
  python3 -I "$fm/tracekit/check/streamcheck.py" "$fm/spec/$2.json" "$tmp/s.ndjson" 2>&1 | head -1 | cut -c1-300
}
record() { # source file cfg at verdict
  echo "$1 $2 $3 $4 $5" >> "$out"
}

if [ -z "${SIMONLY:-}" ]; then
# (a) the recorded streams.
for d in "$fm"/traces/*/; do
  name=$(basename "$d"); m=$(manifest "$name")
  v=$(verdict "$d/stream.ndjson" "$m")
  gzip -9 -c "$d/stream.ndjson" > "$here/traces/$name.ndjson.gz"
  record trace "traces/$name.ndjson.gz" "$(cfgof "$m")" 0 "$v"
  echo "trace $name: $v"
done

# (b) the mutations, on the first stream with a place for each (as validator-tests.sh).
streams=("$fm"/traces/*/stream.ndjson)
for mu in $(python3 -I "$fm/scripts/mutate.py" list); do
  at=""
  for f in "${streams[@]}"; do
    at=$(python3 -I "$fm/scripts/mutate.py" "$mu" "$f" "$tmp/$mu.ndjson") && break
    at=""
  done
  if [ -z "$at" ]; then echo "mutation $mu: no place"; continue; fi
  m=$(manifest "$(basename "$(dirname "$f")")")
  v=$(verdict "$tmp/$mu.ndjson" "$m")
  k=$(echo "$v" | awk '{print $2}')
  case "$v" in
    REJECTED*|VIOLATED*) head -n "$k" "$tmp/$mu.ndjson" | gzip -9 > "$here/mutations/$mu.ndjson.gz" ;;
    *) gzip -9 -c "$tmp/$mu.ndjson" > "$here/mutations/$mu.ndjson.gz" ;;
  esac
  record mutation "mutations/$mu.ndjson.gz" "$(cfgof "$m")" "$at" "$v"
  echo "mutation $mu (at $at): $v"
done

fi

# (c) simulator streams, several modes (scripts/sim-batch.sh's invocations).
( cd "$fm" && go build -o "$tmp/sim" ./sim ) || exit 2
# mode name | nodes | steps | boot | voters | sim flags
modes=(
  "default|3|3000|1||"
  "empty|3|3000|0||"
  "five|5|3000|1||"
  "parallel|3|3000|1||-parallel"
  "async|3|3000|1||-async"
  "asyncsnapreads|3|4000|1||-async -snap -reads"
  "snapreads|3|3000|1||-snap -reads"
  "batch|3|3000|1||-batch -forward"
  "member|5|5000|1|3|-member -calm 4"
  "prevote|3|3000|1||-prevote"
  "nohold|3|3000|1||-async -nohold"
  "splitEH|3|3000|1||-split entries-hardstate"
)
if [ "${MODES:-}" = more ]; then
  modes+=(
    "five-empty|5|3000|0||"
    "member-empty|5|5000|0|3|-member -calm 4"
    "member-async-snap|5|5000|1|3|-member -async -snap -calm 4"
    "member-batch|5|5000|1|3|-member -batch -calm 4"
    "batch-async-reads|3|3000|1||-batch -async -reads -forward -transfer"
    "checkquorum|3|3000|1||-checkquorum"
    "transfer|3|3000|1||-transfer -forward"
    "inflight|3|3000|1||-inflight 2 -snap -snapstatus"
    "stepdown|5|5000|1|3|-member -stepdown -calm 4"
    "splitTEC|3|3000|1||-split term-entries-commit"
    "splitHE|3|3000|1||-split hardstate-entries"
    "member-splitEH|5|5000|1|3|-member -split entries-hardstate -calm 4"
  )
fi
for spec in "${modes[@]}"; do
  IFS='|' read -r mode nodes steps boot voters flags <<< "$spec"
  m=manifest$([ "$nodes" = 5 ] && echo 5)$([ "$boot" = 1 ] || echo -empty)
  [ -n "$voters" ] && m=manifest-m$([ "$boot" = 1 ] || echo -empty)
  for seed in $(seq 1 "$seeds"); do
    f="$tmp/$mode-$seed.ndjson"
    # shellcheck disable=SC2086
    "$tmp/sim" -seed "$seed" -nodes "$nodes" -steps "$steps" -boot="$([ "$boot" = 1 ] && echo true || echo false)" \
      ${voters:+-voters $voters} $flags -out "$f" > /dev/null 2>&1
    v=$(verdict "$f" "$m")
    gzip -9 -c "$f" > "$here/sim/$mode-$seed.ndjson.gz"
    record sim "sim/$mode-$seed.ndjson.gz" "$(cfgof "$m")" 0 "$v"
    echo "sim $mode $seed: $v"
  done
done
