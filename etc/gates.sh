#!/usr/bin/env bash
# The checks a branch passes before it lands on `lean`, in one run (the ones CI runs, plus the
# trust base's and every generator's): the full build, every generated Link.lean, the trust base
# and every collection, the translations (and the examples' go.mod pins), the generated
# initializers, the issues' front matter, the bounds and auth-mode checks, the packages' imports. Prints one line per check and exits 1 if any fails.
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
pk=()
if [ -n "${LAKE_PACKAGES:-}" ]; then pk=(--packages="$LAKE_PACKAGES"); export LAKE_OPTS="--packages=$LAKE_PACKAGES"; fi
fail=0
pids=()
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"; unlink_perennial' EXIT

linked=0
link_perennial() {
  if [ ! -e .lake/packages/perennial ] && [ -n "${PERENNIAL_CHECKOUT:-}" ]; then
    mkdir -p .lake/packages && ln -s "$PERENNIAL_CHECKOUT" .lake/packages/perennial && linked=1
  fi
}
unlink_perennial() {
  if [ "$linked" = 1 ]; then rm -f .lake/packages/perennial; rmdir .lake/packages 2>/dev/null; linked=0; fi
}

# 1. the full build
if lake "${pk[@]}" build > "$tmp/build.log" 2>&1; then
  echo "build: ok ($(grep -o 'Build completed successfully ([0-9]* jobs)' "$tmp/build.log"))"
else
  echo "build: FAILED"; grep -E "error:|error: build failed" "$tmp/build.log" | head -20; fail=1
fi

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
return $fail
}

sec_tcb() {
fail=0
# 3. the trust base and every collection (only after a successful build: tcb-report refuses otherwise)
if python3 etc/tcb-report.py --check > "$tmp/tcb.log" 2>&1; then
  echo "tcb: $(grep 'trust base matches' "$tmp/tcb.log" | tail -1 | sed 's/^tcb: //')"
else
  echo "tcb: FAILED"; grep -v "root theorems\|distinct trust bases" "$tmp/tcb.log" | tail -20; fail=1
fi
coll_ok=0; coll_bad=0
for c in etc/tcb-collections/*.txt; do
  if python3 etc/tcb-report.py --reuse --collection "$c" --check > "$tmp/c.log" 2>&1; then
    coll_ok=$((coll_ok+1))
  else
    coll_bad=$((coll_bad+1)); echo "collection $c: FAILED"; grep -v "root theorems\|distinct trust bases" "$tmp/c.log" | tail -10
  fi
done
echo "collections: $coll_ok match, $coll_bad differ"; [ "$coll_bad" = 0 ] || fail=1
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
# every axiom returning holding an RWMutex reader slot charges a token (begin-tok; reads the sources,
# and the Go sources in .lake/goose that goose.py above clones: so after it, in this section)
python3 etc/reader-slot-check.py || fail=1
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
python3 etc/pbschema-check.py || fail=1
# raft-entsize: etcd's bootstrapped raft configuration has MaxSizePerMsg = 2^20 (`rnStartCfg`'s
# `maxMsg`, a field of the bootstrap contract; examples/entsize, about a second)
if (cd examples && GOWORK=off go test -count=1 ./entsize/ > "$tmp/entsize.log" 2>&1); then
  echo "entsize: ok"
else
  echo "entsize: FAILED"; tail -10 "$tmp/entsize.log"; fail=1
fi
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
# no proof learns a `fmt.Errorf` `%w` error's facts from Perennial's model (reads the sources only)
python3 etc/errorf-wrap-check.py || fail=1
# every trusted statement about an error's description is reviewed for stability (fromerror-stable)
python3 etc/errdesc-check.py || fail=1
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
return $fail
}

sec_premisefix() {
fail=0
# 9. the Go tests behind the closed theorems' premise fixes (examples/premisefix: Go's behavior a
# premise or trust-boundary axiom was restated to; seconds once the packages are compiled)
# (premise fixes 3: skipped while the examples module holds none, `go test` failing on no packages)
if [ -z "$(cd examples && GOWORK=off go list ./premisefix/... 2>/dev/null)" ]; then
  echo "premisefix: none in the examples module"
elif (cd examples && GOWORK=off go test -count=1 ./premisefix/... > "$tmp/pf.log" 2>&1); then
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
  if (cd "$d" && GOWORK=off go test -count=1 ./... > "$tmp/pfn.log" 2>&1); then
    pfn=$((pfn + 1))
  else
    echo "premisefix $d: FAILED"; tail -20 "$tmp/pfn.log"; fail=1
  fi
done
echo "premisefix (own modules): $pfn ok"
return $fail
}

link_perennial
secs=(links tcb goose models issues bounds mode api premisefix)
start=$(date +%s)
for s in "${secs[@]}"; do
  mkdir -p "$tmp/sec.$s"
  ( tmp="$tmp/sec.$s"; "sec_$s" ) > "$tmp/out.$s" 2>&1 &
  pids+=("$!")
done
for i in "${!secs[@]}"; do
  wait "${pids[$i]}" || fail=1
  cat "$tmp/out.${secs[$i]}"
done
unlink_perennial
echo "checks after the build: $(( $(date +%s) - start ))s (in parallel)"

[ "$fail" = 0 ] && echo "gates: all passed" || echo "gates: FAILED"
exit $fail
