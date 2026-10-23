#!/usr/bin/env bash
# The checks a branch passes before it lands on `lean`, in one run (the ones CI runs, plus the
# trust base's and every generator's): the full build, every generated Link.lean, the trust base
# and every collection, the translations (and the examples' go.mod pins), the generated
# initializers, the issues' front matter. Prints one line per check and exits 1 if any fails.
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

# 4. the translations and the examples' go.mod pins, 5. the generated initializers
link_perennial
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
unlink_perennial

# 6. the issues' front matter
if python3 etc/issues-status.py --check > "$tmp/issues.log" 2>&1; then
  echo "issues: ok"
else
  echo "issues: FAILED"; tail -10 "$tmp/issues.log"; fail=1
fi

[ "$fail" = 0 ] && echo "gates: all passed" || echo "gates: FAILED"
exit $fail
