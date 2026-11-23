#!/usr/bin/env bash
# The checks a branch passes before it lands on `lean`, in one run (the ones CI runs, plus the
# trust base's and every generator's): the full build, every generated Link.lean, the trust base
# and every collection, the axiom-tok gate, the translations (and the examples' go.mod pins), the generated
# initializers, the issues' front matter, the bounds, auth-mode and client-port mediation checks, the packages' imports, the import tiers and the interfaces. Prints one line per check and exits 1 if any fails.
#
#   etc/gates.sh                     in a checkout whose .lake/packages holds the pinned Perennial
#   LAKE_PACKAGES=.lake/manifest-stdinit.json PERENNIAL_CHECKOUT=/shared/perennial-std-init \
#     etc/gates.sh                   in a worktree that builds against a Perennial checkout
#                                    through a packages manifest (CLAUDE.md, "The Goose
#                                    translations"); PERENNIAL_CHECKOUT is linked as
#                                    .lake/packages/perennial for goose.py and gen-init.py only
#
# Needs elan's lake, go (GOTOOLCHAIN=go1.27.1 is set), python3.
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
export PATH=/usr/local/go/bin:$HOME/go/bin:$HOME/.elan/bin:$PATH
export GOTOOLCHAIN=${GOTOOLCHAIN:-go1.27.1}
# Lake's artifact cache (shared by the worktrees, keyed by the build traces' input hashes), restored
# into .lake/build (which tcb-report and the other checks read), so that this build and every
# check's `lake build --no-build` agree on what is up to date. Off with LAKE_ARTIFACT_CACHE=false.
export LAKE_ARTIFACT_CACHE=${LAKE_ARTIFACT_CACHE:-true}
export LAKE_RESTORE_ARTIFACTS=${LAKE_RESTORE_ARTIFACTS:-true}
# tcb-report's Lean runs cached across worktrees as model-param's are (etc/lean_cache.py: keyed by
# the run's whole import closure, proofs included): a group none of whose imports changed is read
# from the cache. TCB_CACHE= (empty) runs every group.
export TCB_CACHE=${TCB_CACHE-/shared/tmp/tcb-report-cache}
# The Go tests below use Go's own test cache (keyed by the test binary, so by every Go source and
# dependency it is built from, and by the files and environment variables the test reads; only a
# pass is cached): they read Go code only, never the proofs, so a branch that changes no Go code
# reruns none of them (k8s 7e's cluster tests were 4.5 minutes of every landing, 2026-11-18).
# GATES_GO_COUNT=-count=1 reruns them all. For a result to be reused across runs and worktrees
# (each landing is a branch worktree of its own), `gotest` runs them with a stable TMPDIR (Go
# records the variables a test reads: os.MkdirTemp reads TMPDIR; the tests' own directories are
# unique below it) and -trimpath (no worktree path in the test binary). Measured: k8s 7e's
# TestClientErrorTypes 215s, then (cached) in 0.4s.
gocount=${GATES_GO_COUNT-}
pk=()
if [ -n "${LAKE_PACKAGES:-}" ]; then pk=(--packages="$LAKE_PACKAGES"); export LAKE_OPTS="--packages=$LAKE_PACKAGES"; fi
fail=0
pids=()
# The work directory, and the temporary directory of everything the gates run (TMPDIR: the Go
# tests' data directories, go's build directories, the race tests' logs), on the worktree's disk,
# not /tmp: /tmp is a tmpfs of 7.9G shared by every session (3-4G in use), and each etcd member a
# Go test starts preallocates a 64MB WAL there, so under the premise-fix and k8s tests' clusters it
# filled: premisefix/zaplogger's cluster3.StartCluster panicked in etcdserver.NewServer ("failed to
# create WAL", reproduced on a 100MB tmpfs; 2026-11-17). GATES_TMPDIR overrides the parent.
gtmp=${GATES_TMPDIR:-$root/.lake}
mkdir -p "$gtmp"
tmp=$(mktemp -d "$gtmp/gates.XXXXXX")
mkdir -p "$tmp/tmpdir"
export TMPDIR="$tmp/tmpdir"
trap 'rm -rf "$tmp"; unlink_perennial' EXIT
# the Go tests' TMPDIR (above), on a disk, shared by every gate run
gotmp=${GATES_GO_TMPDIR:-/shared/tmp/gates-gotest}
mkdir -p "$gotmp"
gotest() { TMPDIR="$gotmp" GOFLAGS="${GOFLAGS:+$GOFLAGS }-trimpath" go test $gocount "$@"; }

linked=0
link_perennial() {
  if [ ! -e .lake/packages/perennial ] && [ -n "${PERENNIAL_CHECKOUT:-}" ]; then
    mkdir -p .lake/packages && ln -s "$PERENNIAL_CHECKOUT" .lake/packages/perennial && linked=1
  fi
}
unlink_perennial() {
  if [ "$linked" = 1 ]; then rm -f .lake/packages/perennial; rmdir .lake/packages 2>/dev/null; linked=0; fi
}

# 1. the full build, with the sections that read only the sources (`early`, below) running beside it:
# their failures show within a minute or two instead of after the build, and stop it
# (GATES_FAILFAST=0: let the build finish anyway). Measured 2026-11-21: the build is 9-26 min of a
# gate, the checks after it 1-4 min, and most failed landings that day failed a source-only check
# (links, reader-slot, axiom-tok's stale entries are in tcb, gen-init) after the whole build.

# 2-9 read the build (or only the sources) and nothing writes what another reads: they run in
# parallel, each into its own log, printed in this order once all are done (sections that run one
# check after another, e.g. the trust base then its collections, stay sequential inside); `fail` is
# set by each section in its own subshell and collected from its exit status. The translations
# (goose, gen-init) see .lake/packages/perennial linked for the whole parallel step.
sec_links() {
fail=0
# 2. every generated Link.lean
links=ok
while read -r mode file; do
  if ! python3 etc/gen-link.py "$mode" > "$tmp/l.lean" 2>"$tmp/l.err"; then
    echo "links: gen-link $mode failed"; links=FAILED
  elif ! cmp -s "$tmp/l.lean" "$file"; then
    echo "links: $file differs from gen-link $mode"; links=FAILED
  fi
done < <(grep -o "etc/gen-link.py --[a-z0-9-]* > [^ ]*Link.lean" etc/gen-link.py | sort -u | awk '{print $2, $4}')
bfile=$(grep -o "> [^ ]*Link.lean" etc/gen-btree-link.py | head -1 | cut -c3-)
if ! python3 etc/gen-btree-link.py > "$tmp/l.lean" 2>/dev/null || ! cmp -s "$tmp/l.lean" "$bfile"; then
  echo "links: $bfile differs from gen-btree-link"; links=FAILED
fi
echo "links: $links"; [ "$links" = ok ] || fail=1
# 2b. RaftTla/'s generated copies of the main tree's raft specs and proofs (raft's `with_tla` build)
if python3 etc/gen-raft-tla.py --check > "$tmp/tla.log" 2>&1; then
  echo "$(tail -1 "$tmp/tla.log")"
else
  echo "gen-raft-tla: FAILED"; tail -10 "$tmp/tla.log"; fail=1
fi
# (the parts RaftNoAx/ and KvNet/: one summary line each)
if python3 etc/copy-part.py --check > "$tmp/cp.log" 2>&1; then
  grep '^copy-part: [A-Za-z]*: ' "$tmp/cp.log"
else
  echo "copy-part: FAILED"; tail -10 "$tmp/cp.log"; fail=1
fi
return $fail
}

sec_tcb() {
fail=0
# its own memory cap for the axiom-tok gate (systemd-run, where there is one; only where it works: a
# session without a login's polkit rights gets "Access denied", 2026-11-15)
cap=()
if command -v systemd-run > /dev/null 2>&1 && systemd-run --scope -q -p MemoryMax=24G true > /dev/null 2>&1; then
  cap=(systemd-run --scope -q -p MemoryMax=24G)
fi
# 3b's Lean runs, started beside 3's: the axiom-tok gate walks the axioms of .lake/tcb.json, which
# the trust-base check below rewrites; they are run now on the axioms of the .lake/tcb.json already
# here (a previous run's), and used only if the new one lists exactly the same axioms in the same
# order (the same input, so the same output); otherwise run again after it. One lane (TCB_JOBS=1):
# its peak beside 3's Lean runs stays one group's, under 10 GiB.
spec=0
if [ -f .lake/tcb.json ] && python3 etc/axiom-tok-check.py --dump-names > "$tmp/names.spec" 2> /dev/null \
    && [ -s "$tmp/names.spec" ]; then
  ( TCB_JOBS=1 "${cap[@]}" python3 etc/axiom-tok-check.py --lean-only --names "$tmp/names.spec" \
      --raw "$tmp/atok.spec.jsonl" > "$tmp/atok.spec.log" 2>&1; echo $? > "$tmp/atok.spec.status" ) &
  spec_pid=$!; spec=1
fi
# 3. the trust base and every collection (only after a successful build: tcb-report refuses otherwise)
if python3 etc/tcb-report.py --check > "$tmp/tcb.log" 2>&1; then
  echo "tcb: $(grep 'trust base matches' "$tmp/tcb.log" | tail -1 | sed 's/^tcb: //')"
else
  echo "tcb: FAILED"; grep -v "root theorems\|distinct trust bases" "$tmp/tcb.log" | tail -20; fail=1
fi
# the collections, in one run (the JSON loaded once; each collection checked as on its own: 68
# runs of 5.6s each, nearly all of it parsing the JSON, took six minutes), beside the axiom-tok gate
# below: both only read the .lake/tcb.json the check above wrote
ncoll=$(ls etc/tcb-collections/*.txt | wc -l)
( python3 etc/tcb-report.py --reuse --collection etc/tcb-collections/*.txt --check > "$tmp/c.log" 2>&1
  echo $? > "$tmp/c.status" ) &
coll_pid=$!
# 3a. no proof steps into Perennial's `fmt.Errorf` model outside the reviewed declarations (the proof
# terms, as etc/tcb-report.lean marks them; reads the .lake/tcb.json the trust-base check above
# wrote, so after it, in this section)
python3 etc/errorf-wrap-check.py --reuse || fail=1
# 3b. the axiom-tok gate (per-type stage B, Scope r5 §5.1): no trusted statement lets its user
# obtain tokens or resources it chose beyond what it gives, but for the entries of
# etc/axiom-tok-allow.txt; reads the .lake/tcb.json the trust-base check above wrote (so after it,
# in this section; its Lean runs from above when they walked the same axioms). A full run: about
# 6 minutes interpreted, 75s native (2026-11-17), 9 GiB peak per group.
atok=(--raw "$tmp/atok.jsonl")
atok_from="run after the trust-base check"
if [ "$spec" = 1 ]; then
  wait "$spec_pid"
  python3 etc/axiom-tok-check.py --dump-names > "$tmp/names.now" 2> /dev/null
  if [ "$(cat "$tmp/atok.spec.status" 2>/dev/null)" = 0 ] && [ -s "$tmp/names.now" ] \
      && cmp -s "$tmp/names.spec" "$tmp/names.now"; then
    cp "$tmp/atok.spec.jsonl" "$tmp/atok.jsonl"
    atok=(--reuse-raw "$tmp/atok.jsonl"); atok_from="Lean runs beside the trust-base check"
  else
    atok_from="run after the trust-base check: its axioms changed"
  fi
fi
if "${cap[@]}" python3 etc/axiom-tok-check.py --check "${atok[@]}" > "$tmp/atok.log" 2>&1; then
  echo "axiom-tok: $(tail -1 "$tmp/atok.log" | sed 's/^axiom-tok: //') ($atok_from)"
else
  echo "axiom-tok: FAILED ($atok_from)"; grep -A40 "need an entry (rule 8)\|^Unknown\|^Truncations\|^Entry keys\|^Stale\|FAILED\|Error\|error" "$tmp/atok.log" | head -40; fail=1
fi
# its selftests, and the real axioms they name (`real-pass`) in the run above
"${cap[@]}" python3 etc/axiom-tok-check.py --selftest --reuse-raw "$tmp/atok.jsonl" > "$tmp/atoks.log" 2>&1 || { echo "axiom-tok selftest: FAILED"; grep "FAIL\|error" "$tmp/atoks.log" | head -20; fail=1; }
wait "$coll_pid"
coll_ok=$(grep -c "^tcb: trust base matches" "$tmp/c.log")
coll_bad=$((ncoll - coll_ok))
if [ "$(cat "$tmp/c.status" 2>/dev/null)" != 0 ] || [ "$coll_bad" != 0 ]; then
  [ "$coll_bad" != 0 ] || coll_bad="?"
  grep "^tcb: collection .*: FAILED" "$tmp/c.log" | sed 's/^tcb: //'
  grep -v "root theorems\|distinct trust bases\|^tcb: trust base matches" "$tmp/c.log" | tail -20; fail=1
fi
echo "collections: $coll_ok match, $coll_bad differ"
return $fail
}

sec_goose() {
fail=0
# 4. the translations and the examples' go.mod pins, 5. the generated initializers
if python3 etc/goose.py --check > "$tmp/goose.log" 2>&1; then
  echo "goose: ok ($(grep -c 'is up to date' "$tmp/goose.log") projects up to date)"
else
  echo "goose: FAILED"; grep "^goose.py:" "$tmp/goose.log" | grep -v "up to date" | head -20; fail=1
fi
if python3 etc/gen-init.py --check > "$tmp/init.log" 2>&1; then
  echo "gen-init: $(tail -1 "$tmp/init.log" | sed 's/^gen-init: //')"
else
  echo "gen-init: FAILED"; tail -10 "$tmp/init.log"; fail=1
fi
# SpecPlan's generated package-init specs (SpecPlan/Spec/PkgInit/, etc/gen-specs-pkginit.py): a
# stale one can still build, so only this check sees it (putget-dist, 2026-11-23)
if python3 etc/gen-specs-pkginit.py --check > "$tmp/specpkginit.log" 2>&1; then
  echo "gen-specs-pkginit: ok"
else
  echo "gen-specs-pkginit: FAILED (run etc/gen-specs-pkginit.py)"; head -10 "$tmp/specpkginit.log"; fail=1
fi
# the k8s API objects' deep values and deep copies, and the Goose configuration they translate
# (Proof/k8s_io/api/Deep.lean, Proof/k8s_io/api/DeepCopy/, the generated blocks of the tomls)
if python3 etc/gen-k8s-deep.py --check > "$tmp/k8sdeep.log" 2>&1; then
  echo "gen-k8s-deep: ok"
else
  echo "gen-k8s-deep: FAILED"; tail -5 "$tmp/k8sdeep.log"; fail=1
fi
# the trusted protobuf schemas (PbSchema.lean's generated region) are the registered descriptors'
# (models/pbdesc, run in examples/; etc/gen-pbschema.py, protobuf stage 0')
if python3 etc/gen-pbschema.py --check > "$tmp/pbschemagen.log" 2>&1; then
  echo "$(tail -1 "$tmp/pbschemagen.log")"
else
  echo "gen-pbschema: FAILED"; tail -10 "$tmp/pbschemagen.log"; fail=1
fi
# every axiom returning holding an RWMutex reader slot charges a token (begin-tok; reads the sources,
# and the Go sources in .lake/goose that goose.py above clones: so after it, in this section)
python3 etc/reader-slot-check.py || fail=1
# every registration on etcd's client port has a row in etc/auth-table.txt with the specs that carry
# its access check, none weaker than etc/auth-mediation-baseline.txt (notes/auth-mediation-scope.md,
# M0; reads the Go sources in .lake/goose that goose.py above clones, and the specs: so after it)
if python3 etc/auth-mediation-check.py --check > "$tmp/authmed.log" 2>&1; then
  echo "$(tail -1 "$tmp/authmed.log")"
else
  echo "auth-mediation: FAILED"; grep -v "^auth-mediation: ok" "$tmp/authmed.log" | head -20; fail=1
fi
return $fail
}

sec_models() {
fail=0
# 5b. the per-type message models (stage A): no trusted statement lets its user choose a message
# model (etc/model-param-check.py, rules 1-7 with their negative tests), and the trusted protobuf
# schemas agree with the Go descriptors (etc/pbschema-check.py, with its negative tests); both read
# the built .oleans, so only after a successful build
# (its Lean runs are cached across worktrees by a content hash of their inputs; `--no-cache` to bypass)
python3 etc/model-param-check.py || fail=1
# phase 7 S2 (O2): the specs a service table holds reach no HeapGS (etc/heapfree-check.py)
python3 etc/heapfree-check.py || fail=1
python3 etc/pbschema-check.py || fail=1
# raft-entsize: etcd's bootstrapped raft configuration has MaxSizePerMsg = 2^20 (`rnStartCfg`'s
# `maxMsg`, a field of the bootstrap contract; examples/entsize, about a second)
if (cd examples && GOWORK=off gotest ./entsize/ > "$tmp/entsize.log" 2>&1); then
  echo "entsize: ok"
else
  echo "entsize: FAILED"; tail -10 "$tmp/entsize.log"; fail=1
fi
# protobuf stages S1/S2 (#37): the wire codecs' vectors modules EntryWireVectors.lean,
# MessageWireVectors.lean, RecordWireVectors.lean and apply/IrrWireVectors.lean (whose #guards the build checks against the Lean
# codecs) are what examples/pbschema/wirevectors{,_s2}_test.go generate from protobuf-go
# (examples/go.mod's pin); TestMessageDepthLimit checks the decoder's recursion limit in Go
if (cd examples && GOWORK=off gotest -run '^(TestWireVectors|TestMessageWireVectors|TestRecordWireVectors|TestIrrWireVectors|TestMessageDepthLimit)$' ./pbschema/ > "$tmp/wirevec.log" 2>&1); then
  echo "wirevectors: ok"
else
  echo "wirevectors: FAILED"; tail -10 "$tmp/wirevec.log"; fail=1
fi
# the library models (models/, models/README.md; notes/dsverify-net-port-plan.md phase 5): every
# generated codec is exactly its generator's output for its derived input (pbgen: the roots'
# descriptors; --check), every protobuf.toml in the tree (but old/) is one of them, the codec helpers
# against protowire, unicode/utf8 and encoding/json, the generated codecs against protobuf-go and
# encoding/json, pbgen's and jsongen's random differential tests and refusals
# (models/internal/{pbgenrand,jsongenrand}), and pbgen's and jsongen's codecs of etcd's types
# (examples/models/{pbetcd,jsonetcd})
nm=0
: > "$tmp/nm.log"
pbinputs="models/internal/pbdifftest/protobuf.toml:models/internal/pbdifftest/codec:codec
examples/models/pbetcd/protobuf.toml:examples/models/pbetcd:pbetcd"
for x in $pbinputs; do
  IFS=: read -r t o p <<< "$x"
  python3 models/protobuf/pbgen.py "$t" "$o" --pkg "$p" --check >> "$tmp/nm.log" 2>&1 || nm=1
done
for t in $(git ls-files '*protobuf.toml' ':!old/'); do  # old/: reference copies, not built
  grep -q "^$t:" <<< "$pbinputs" || { echo "models: $t is not checked by the gates (add it)" >> "$tmp/nm.log"; nm=1; }
done
# jsongen: every toml with a [json] table (but in old/) is checked (the dump by reflection included);
# jsongen's random-type differential test and refusals run in models' go test (internal/jsongenrand)
jsoninputs="models/internal/jsondifftest/json.toml:models/internal/jsondifftest/codec:codec
models/internal/jsonvsr/json.toml:models/internal/jsonvsr/codec:codec
examples/models/jsonetcd/json.toml:examples/models/jsonetcd:jsonetcd
models/internal/jsonpkgtest/json.toml:models/internal/jsonpkgtest:jsonpkgtest"
for x in $jsoninputs; do
  IFS=: read -r t o p <<< "$x"
  python3 models/json/jsongen.py "$t" "$o" --pkg "$p" --check >> "$tmp/nm.log" 2>&1 || nm=1
done
# (#24 J3) jsongen's same-package methods (JSONModel*, which the encoding/json model's dispatch calls
# by a value's method set) are reserved: no Go code but the generated json_model_gen*.go files and
# the model's dispatch (models/encoding/json) names them; the generated methods against the real
# encoding/json (the netmodel build's test of internal/jsonpkgtest), and in the forks' packages of
# etc/goose.py's jsonmodel_roots (examples/models/jsonetcd/jsonmodel_forks.py, which also checks the
# names in the forks at the pins)
if git grep -nE '\bJSONModel[A-Za-z]*' -- '*.go' ':!old/' ':!**/json_model_gen.go' ':!**/json_model_gen_test.go' \
     ':!models/encoding/json/' >> "$tmp/nm.log" 2>&1; then
  echo "models: Go code other than the generated methods names JSONModel* (above)" >> "$tmp/nm.log"; nm=1
fi
(cd models && GOWORK=off gotest -tags netmodel -run '^TestJSON' ./internal/jsonpkgtest/) >> "$tmp/nm.log" 2>&1 || nm=1
python3 examples/models/jsonetcd/jsonmodel_forks.py >> "$tmp/nm.log" 2>&1 || nm=1
for t in $(git grep -l '^\[json\]' -- '*.toml' ':!old/'); do  # old/: reference copies, not built
  grep -q "^$t:" <<< "$jsoninputs" || { echo "models: $t is not checked by the gates (add it)" >> "$tmp/nm.log"; nm=1; }
done
# (the models' Go is go1.27.3's, etc/goose.py's GO_TOOLCHAIN: net/http's golden transcripts and the
# overlays of net/rpc, net/http and encoding/json are of that release, not of the gates' go1.27.1)
(cd models && export GOTOOLCHAIN=go1.27.3 && GOWORK=off go vet ./... && GOWORK=off gotest ./...) \
  >> "$tmp/nm.log" 2>&1 || nm=1
# the net/rpc and net/http models (models/net/; phase 5.2): rpcgen's codec is its output for the
# derived input (--check, inside run.sh), and the differential tests pass against the real packages
# and against the models (an overlay of the toolchain's source, models/goroot.py)
GOTOOLCHAIN=go1.27.3 models/internal/rpcdifftest/run.sh >> "$tmp/nm.log" 2>&1 || nm=1
(cd examples && GOWORK=off gotest ./models/...) >> "$tmp/nm.log" 2>&1 || nm=1
# the grpc model (models/grpc; phase 5.4): its differential test against grpc-go v1.84.0 and the
# model, the model's invariants with its choices random, and examples/ built against the model
models/internal/grpcdifftest/run.sh >> "$tmp/nm.log" 2>&1 || nm=1
# the encoding/json model (models/encoding/json): its stream tests against the real encoding/json's
# golden transcripts, in the real build and in the model build (an overlay: goroot.py)
models/internal/jsonstreamtest/run.sh >> "$tmp/nm.log" 2>&1 || nm=1
# the third-party library models (models/{gods,uuid,concurrent-map}, the dsverify kits'): the same
# tests against gods v1.18.1, uuid v1.3.1, concurrent-map v1.0.0 and against the models, with equal
# transcripts
models/internal/tpdifftest/run.sh >> "$tmp/nm.log" 2>&1 || nm=1
# the log/slog model (models/log/slog): the same tests against Go's log/slog and the model (an
# overlay: goroot.py), with equal transcripts
models/internal/slogdifftest/run.sh >> "$tmp/nm.log" 2>&1 || nm=1
if [ $nm = 0 ]; then echo "models: ok"; else echo "models: FAILED"; tail -20 "$tmp/nm.log"; fail=1; fi
# clients on machines of their own (examples/lib/remote, notes/remote-port-plan.md): the library's and
# its counter instance's tests over real sockets (fault proxy, the four commands as processes, a
# double-apply control), and lintest's per-client driver
nr=0
( (cd examples/lib/remote && GOWORK=off go vet ./... && GOWORK=off gotest ./...) \
  && (cd examples/lib/lintest && GOWORK=off gotest ./perclient) ) > "$tmp/remote.log" 2>&1 || nr=1
if [ $nr = 0 ]; then echo "remote: ok"; else echo "remote: FAILED"; tail -20 "$tmp/remote.log"; fail=1; fi
# the per-type stage's joint landing: stage A's restated swMsgBound_phys is gone (raft-entsize
# deleted it); etc/joint-landing-check.py refuses it in the baselines (reads them only), with its
# selftest
python3 etc/joint-landing-check.py --selftest || fail=1
python3 etc/joint-landing-check.py || fail=1
return $fail
}

sec_issues() {
fail=0
# 6. the issues' front matter
if python3 etc/issues-status.py --check > "$tmp/issues.log" 2>&1; then
  echo "issues: ok"
else
  echo "issues: FAILED"; tail -10 "$tmp/issues.log"; fail=1
fi
# the notes' merge drivers (etc/merge-status.py; .gitattributes): replays this week's real merges of
# notes/STATUS.md and notes/status-history.md, and synthetic cases (reads git only; ~15s)
python3 etc/merge-status.py --selftest || fail=1
# every trusted statement about an error's description is reviewed for stability (fromerror-stable)
python3 etc/errdesc-check.py || fail=1
# the pinned Perennial has no WithCancelCause spec, which context.bgCancelChild's soundness needs
# (k8s 7f-4, Addendum T-i; reads the sources only)
python3 etc/bgcancel-check.py || fail=1
# the k8s etcd3 driver's copy of Kubernetes' checker (examples/k8s/etcd3/correctness) is upstream's
# at the driver's k8s.io/apiserver pin plus etc/k8s-correctness/d30g.patch, byte for byte (k8s 7g,
# notes/k8s-7g-scope.md §1.1; needs go and the module cache; seconds)
python3 etc/k8s-correctness-check.py || fail=1
# the default feature gate's environment assumption (B5, k8s 7f-5 T5-c, Gate.lean): every
# feature-gate mutator in the programs' compiled closures has its verdict in
# etc/featuregate-allow.txt (needs go and the module cache; seconds)
python3 etc/featuregate-check.py || fail=1
return $fail
}

sec_bounds() {
fail=0
# 7. the bound reasoning stays with its owners (notes/bounds-plan.md, B0; reads the sources only)
if python3 etc/bounds-check.py --check > "$tmp/bounds.log" 2>&1; then
  echo "$(tail -1 "$tmp/bounds.log")"
  grep "down from" "$tmp/bounds.log" | head -5
else
  echo "bounds: FAILED"; grep -v "^bounds: ok" "$tmp/bounds.log" | head -20; fail=1
fi
return $fail
}

sec_mode() {
fail=0
# 7b. the auth-mode divergence outside the auth component only goes down (the auth component's
# stage 2, D2: a ratchet; reads the sources only)
if python3 etc/mode-check.py --check > "$tmp/mode.log" 2>&1; then
  echo "$(tail -1 "$tmp/mode.log")"
  grep "down from" "$tmp/mode.log" | head -5
else
  echo "mode: FAILED"; grep -v "^mode: ok" "$tmp/mode.log" | head -20; fail=1
fi
return $fail
}

sec_api() {
fail=0
# 8. each package's clients import only its importable modules (etc/api/<pkg>.txt; CLAUDE.md,
# "Package APIs"), and only the listed modules `import all` a sealed one (etc/import-all.txt; the
# backend-auth-split stage's Q6, 2026-11-02); both read the sources only
api=ok
for c in etc/api/*.txt; do
  case "$c" in *-layout.txt) continue ;; esac
  if ! python3 etc/api-check.py "$c" --check > "$tmp/api.log" 2>&1; then
    echo "api $c: FAILED"; grep -v "^warning" "$tmp/api.log" | tail -10; api=FAILED
  fi
done
echo "api: $api"; [ "$api" = ok ] || fail=1
if python3 etc/import-all-check.py --check > "$tmp/ia.log" 2>&1; then
  echo "$(tail -1 "$tmp/ia.log")"
else
  echo "import-all: FAILED"; head -20 "$tmp/ia.log"; fail=1
fi
# the import tiers: no spec, definition or proof module imports a proof or linking module, but the
# known ones of etc/tier-baseline.txt (CLAUDE.md, "Import tiers"; reads the sources only, seconds)
if python3 etc/tier-check.py --check > "$tmp/tier.log" 2>&1; then
  echo "$(tail -1 "$tmp/tier.log")"
else
  echo "tier: FAILED"; head -20 "$tmp/tier.log"; fail=1
fi
return $fail
}

sec_iface() {
fail=0
# 8b. the checked-in interfaces (`interface/`) are what the build exports, with no new layout
# violation: CI's "Check the packages' interfaces" loop, verbatim (reads the build; `$LAKE_OPTS`
# carries `--packages`). Added 2026-11-13: CI failed on it since a1e57a9676 while land.sh passed.
# The packages at once (each about 30s, mostly its own parallel pretty-printing; one after another
# they were 200s of the gate, 2026-11-18).
iface=ok
pids=()
for c in etc/api/*.txt; do
  case "$c" in *-layout.txt) continue ;; esac
  b=$(basename "$c" .txt)
  ( python3 etc/gen-interface.py "$c" --check --layout > "$tmp/iface.$b.log" 2>&1
    echo $? > "$tmp/iface.$b.status" ) &
  pids+=($!)
done
wait "${pids[@]}"
for c in etc/api/*.txt; do
  case "$c" in *-layout.txt) continue ;; esac
  b=$(basename "$c" .txt)
  if [ "$(cat "$tmp/iface.$b.status" 2>/dev/null)" != 0 ]; then
    echo "interface $c: FAILED"; tail -20 "$tmp/iface.$b.log"; iface=FAILED
  fi
done
echo "interfaces: $iface"; [ "$iface" = ok ] || fail=1
return $fail
}

sec_premisefix() {
fail=0
# 9. the Go tests behind the closed theorems' premise fixes (examples/premisefix: Go's behavior a
# premise or trust-boundary axiom was restated to; seconds once the packages are compiled)
# (premise fixes 3: skipped while the examples module holds none, `go test` failing on no packages)
if [ -z "$(cd examples && GOWORK=off go list ./premisefix/... 2>/dev/null)" ]; then
  echo "premisefix: none in the examples module"
elif (cd examples && GOWORK=off gotest ./premisefix/... > "$tmp/pf.log" 2>&1); then
  echo "premisefix: ok ($(grep -c '^ok' "$tmp/pf.log") packages)"
else
  echo "premisefix: FAILED"; tail -20 "$tmp/pf.log"; fail=1
fi
# 9b. ... and those in a Go module of their own under examples/premisefix (a test that needs a
# dependency the examples module does not require: premise fixes 3, k8s.io/apiserver), which
# `./premisefix/...` above skips
pfn=0
for m in $(find examples/premisefix -mindepth 2 -name go.mod 2>/dev/null | sort); do
  d=$(dirname "$m")
  if (cd "$d" && GOWORK=off gotest ./... > "$tmp/pfn.log" 2>&1); then
    pfn=$((pfn + 1))
  else
    echo "premisefix $d: FAILED"; tail -20 "$tmp/pfn.log"; fail=1
  fi
done
echo "premisefix (own modules): $pfn ok"
return $fail
}

sec_k8s7e() {
fail=0
# 9c-9f: k8s 7e's Go evidence (Go tests in their own modules; minutes)
# 9c. the Go evidence for k8s 7e-1's restated trust statements (decided by etcd-grove-81): every
# error kubernetes.Client returns has one of clientErrTys' four dynamic types, under partitions,
# deadlines and a closed client (TestClientErrorTypes, about 4 minutes), and etcd's per-RPC
# credential never errs (TestCredentialNilError, perRPCCredsOk)
# A run whose in-process cluster fails to start ("StartCluster failed": a port taken by another
# gate run's cluster under the parallel load, 2026-11-12, three times) is retried, up to 3 attempts;
# any other failure fails at once.
cet_try=0; cet_ok=0; cet_miss=
while [ $cet_try -lt 3 ]; do
  cet_try=$((cet_try + 1))
  if (cd examples/k8s/etcd3 && GOWORK=off gotest -timeout 30m \
      -run '^(TestClientErrorTypes|TestCredentialNilError)$' . > "$tmp/cet.log" 2>&1); then
    cet_ok=1; break
  fi
  grep -qi "startCluster failed" "$tmp/cet.log" || break  # the test prints "startCluster failed"
  cet_miss="$cet_miss attempt $cet_try: StartCluster failed;"
done
if [ $cet_ok = 1 ]; then
  echo "k8s client error types: ok (attempt $cet_try of 3${cet_miss:+;$cet_miss})"
else
  echo "k8s client error types: FAILED (attempt $cet_try${cet_miss:+;$cet_miss})"; tail -20 "$tmp/cet.log"; fail=1
fi

# 9e. the attack programs behind grpcInvokerOk's attempt-level error types (k8s 7e Freeze review):
# grpc-go's bare invoker returns nil or *status.Error under etcd's configuration (seconds)
if (cd examples/k8s7e1attack && GOWORK=off gotest ./... > "$tmp/k7a.log" 2>&1); then
  echo "k8s 7e-1 attack programs: ok"
else
  echo "k8s 7e-1 attack programs: FAILED"; tail -20 "$tmp/k7a.log"; fail=1
fi
# 9f. k8s 7e-2's Go evidence for its trusted texts (examples/k8s7e2attack, at the etcd pin of
# etc/goose.py: rpctypes' error values, apierrors' views, tracing's contexts, reflect; seconds)
if (cd examples/k8s7e2attack && GOWORK=off gotest ./... > "$tmp/k72.log" 2>&1); then
  echo "k8s 7e-2 attack tests: ok"
else
  echo "k8s 7e-2 attack tests: FAILED"; tail -20 "$tmp/k72.log"; fail=1
fi
# 9d. k8s 7e-1's owned reply Kvs (recvOwn, decided by etcd-grove-81): no race on the reply's Kvs
# array after Invoke, with retries, in the default configuration (EnableTracing off)
if (cd examples/k8s/etcd3 && GOWORK=off gotest -race -timeout 10m \
    -run '^TestDefaultNoRace$' . > "$tmp/kvo.log" 2>&1); then
  echo "k8s owned reply Kvs: ok"
else
  echo "k8s owned reply Kvs: FAILED"; tail -20 "$tmp/kvo.log"; fail=1
fi
# ... and its positive control (the k8s 7e Freeze review): the same harness with grpc's tracing on,
# which keeps the reply, must FAIL under -race with a data race (TestTracingRace, gated by
# K8S_KVSOWN_CONTROL=1), so that a passing TestDefaultNoRace means something
# A run may miss the race under the gates' parallel load (it did once, 2026-11-11): retry a run
# that misses it, up to 3 attempts; pass once one attempt fails with a data race reported.
# Always -count=1: Go caches a passing test, so one missed race (a pass) was replayed as
# `ok (cached)` by every later run and attempt, failing every landing (2026-11-19).
kvc_ok=0; kvc_miss=""
for kvc_try in 1 2 3; do
  if (cd examples/k8s/etcd3 && K8S_KVSOWN_CONTROL=1 GOWORK=off gotest -count=1 -race -timeout 10m \
      -run '^TestTracingRace$' . > "$tmp/kvc.$kvc_try.log" 2>&1); then
    kvc_miss="$kvc_miss attempt $kvc_try: passed (no race detected);"
  elif grep -q 'WARNING: DATA RACE' "$tmp/kvc.$kvc_try.log"; then
    kvc_ok=1; break
  else
    kvc_miss="$kvc_miss attempt $kvc_try: failed without a data race;"
  fi
done
if [ "$kvc_ok" = 1 ]; then
  echo "k8s owned reply Kvs control: ok (race detected with tracing on, attempt $kvc_try of 3${kvc_miss:+;$kvc_miss})"
else
  echo "k8s owned reply Kvs control: FAILED (all 3 attempts missed the race with tracing on:$kvc_miss)"
  tail -20 "$tmp/kvc.3.log"; fail=1
fi
return $fail
}

secs=(links tcb goose models issues bounds mode api iface premisefix k8s7e)
# sections that read the build: tcb (Lean runs, tcb.json), models (model-param's and pbschema's Lean
# runs), iface (gen-interface reads the .oleans); the others read only the sources and the Go code.
# With PERENNIAL_CHECKOUT, the translations need .lake/packages/perennial linked, which the build
# must not see: then every section waits for the build, as before.
early=(links goose issues bounds mode api premisefix k8s7e)
[ -n "${PERENNIAL_CHECKOUT:-}" ] && early=()
declare -A spid
run_sec() {
  local s=$1; mkdir -p "$tmp/sec.$s"
  ( tmp="$tmp/sec.$s"; t0=$(date +%s); "sec_$s"; st=$?; echo $(( $(date +%s) - t0 )) > "$tmp/time"; echo $st > "$tmp/status"; exit $st ) > "$tmp/out.$s" 2>&1 &
  spid[$s]=$!
}
for s in "${early[@]}"; do run_sec "$s"; done
bstart=$(date +%s)
setsid lake "${pk[@]}" build > "$tmp/build.log" 2>&1 &
bpid=$!
stopped=
while kill -0 "$bpid" 2>/dev/null; do
  if [ "${GATES_FAILFAST:-1}" = 1 ]; then
    for s in "${early[@]}"; do
      st=$(cat "$tmp/sec.$s/status" 2>/dev/null)
      if [ -n "$st" ] && [ "$st" != 0 ]; then stopped=$s; break; fi
    done
    if [ -n "$stopped" ]; then
      kill -TERM -- "-$bpid" 2>/dev/null; wait "$bpid" 2>/dev/null
      # a killed write may leave an empty artifact in the shared cache (as a VM preemption did,
      # 2026-11-21): remove the empty files the last minutes wrote, before anyone restores them
      [ -n "${LAKE_CACHE_DIR:-}" ] && find "$LAKE_CACHE_DIR" -xdev -type f -size 0 ! -name '*.tmp*' -mmin -30 -delete 2>/dev/null
      break
    fi
  fi
  sleep 5
done
wait "$bpid"; bst=$?
if [ -n "$stopped" ]; then
  echo "build: STOPPED after $(( $(date +%s) - bstart ))s (section $stopped failed; GATES_FAILFAST=0 to build anyway)"; fail=1
elif [ $bst = 0 ]; then
  echo "build: ok ($(grep -o 'Build completed successfully ([0-9]* jobs)' "$tmp/build.log"), $(( $(date +%s) - bstart ))s)"
else
  echo "build: FAILED"; grep -E "error:|error: build failed" "$tmp/build.log" | head -20; fail=1
fi
start=$(date +%s)
link_perennial
if [ -z "$stopped" ]; then
  for s in "${secs[@]}"; do [ -n "${spid[$s]:-}" ] || run_sec "$s"; done
fi
times=
for s in "${secs[@]}"; do
  [ -n "${spid[$s]:-}" ] || continue
  wait "${spid[$s]}" || fail=1
  cat "$tmp/out.$s"
  times="$times $s $(cat "$tmp/sec.$s/time" 2>/dev/null)s"
done
unlink_perennial
echo "checks after the build: $(( $(date +%s) - start ))s (in parallel; the source-only ones started with the build; per section:$times)"

[ "$fail" = 0 ] && echo "gates: all passed" || echo "gates: FAILED"
exit $fail
