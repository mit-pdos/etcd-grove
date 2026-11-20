#!/bin/bash
# goalbuild.sh WORK: build a seeded work tree's Lean side from scratch, as a run starts it (kit v2,
# notes/kit-v2.md): the fixed files in WORK/kit/lean (DsvStatement, DsvNet, the harness's modules
# in dependency order, the generated statement and residue), Goose's output for the fork
# (its generated goose.sh, against those modules), then Goal.lean (goal_spec is `sorry` in a
# fresh seed) and the final check's GoalCheck.lean, whose axioms are printed.
# Output in WORK/kit/build (oleans) and WORK/fork/*/lean. Exit 0 if everything elaborates.
# Environment: PERENNIAL, GOOSE_BIN, LEAN (defaults: the lab's).
# HARNESS_PREBUILT=DIR (a harness build with its STAMP: harness/lean/leancache.sh harness): a fixed
# harness module (and DsvStatement, DsvNet) is copied from DIR/build instead of built when DIR's
# STAMP has this LEAN's and this PERENNIAL's ids (stamp.sh) and the module's source, and that of
# every module it imports, byte for byte (by sha256); anything else is built as without it.
set -euo pipefail
W=$(cd "${1:?usage: goalbuild.sh WORK}" && pwd)
H=$(cd "$(dirname "$0")/../lean" && pwd)          # the lab's harness/lean (for the module order)
D=${PERENNIAL:-/shared/perennial-4c8617a9e}
P=$D/.lake/packages
export LEAN=${LEAN:-/shared/dsverify-lab/cache/tools/leanprover--lean4---v4.34.1/bin/lean}
export GOOSE_BIN=${GOOSE_BIN:-/shared/dsverify-lab/cache/epaxos/bin}
export PERENNIAL=$D
KL=$W/kit/lean; B=$W/kit/build
F=$(ls -d "$W"/fork/*/ | head -1); F=${F%/}
mkdir -p "$B"
LP=$D/.lake/build/lib/lean:$P/Qq/.lake/build/lib/lean:$P/batteries/.lake/build/lib/lean:$P/iris/Iris/.lake/build/lib/lean
# HARNESS_PREBUILT: PRE[module]=its source's sha256 in the prebuilt STAMP, when the STAMP fits
declare -A PRE=() REUSED=()
if [ -n "${HARNESS_PREBUILT:-}" ]; then
  st=$HARNESS_PREBUILT/STAMP
  if [ -f "$st" ] && grep -qxF "lean $("$H/stamp.sh" lean-id "$LEAN")" "$st" &&
      grep -qxF "perennial $("$H/stamp.sh" perennial-id "$D")" "$st"; then
    while read -r kind h f; do
      case $kind:$f in
      src:harness/lean/Harness/*.lean) f=${f#harness/lean/}; PRE[${f%.lean}]=$h ;;
      src:statement/*.lean) f=${f#statement/}; PRE[${f%.lean}]=$h ;;
      esac
    done <"$st"
    echo "goalbuild: HARNESS_PREBUILT $HARNESS_PREBUILT fits this lean and Perennial (${#PRE[@]} modules)"
  else
    echo "goalbuild: HARNESS_PREBUILT $HARNESS_PREBUILT is for another lean or Perennial: not used"
  fi
fi
# reusable ROOT MODULE: the prebuilt output is what building it here would give (same source, and
# every module it imports reused or Perennial's or its dependencies' or Lean's)
reusable() {
  local i
  [ -n "${PRE[$2]:-}" ] && [ -f "$HARNESS_PREBUILT/build/$2.olean" ] || return 1
  [ "$(sha256sum <"$1/$2.lean" | cut -c1-64)" = "${PRE[$2]}" ] || return 1
  # every name on an import line (public, meta, private, all; a comment's "import x" only adds a
  # dependency, which can only prevent reuse)
  for i in $(awk '/^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]/ {
      on=0; for (j = 1; j <= NF; j++) { if ($j == "--") break; if (on && $j != "all") print $j; if ($j == "import") on=1 } }' "$1/$2.lean"); do
    case $i in
    Perennial|Perennial.*|PerennialMeta|PerennialMeta.*|Iris|Iris.*|Batteries|Batteries.*|Qq|Qq.*|Lean|Lean.*|Init|Init.*|Std|Std.*) ;;
    *) [ -n "${REUSED[${i//.//}]:-}" ] || return 1 ;;
    esac
  done
}
build() {  # build ROOT MODULE (a path without .lean)
  mkdir -p "$B/$(dirname "$2")"
  if [ -n "${HARNESS_PREBUILT:-}" ] && reusable "$1" "$2"; then
    for e in olean olean.private olean.server ilean ir ir.sig; do
      [ -f "$HARNESS_PREBUILT/build/$2.$e" ] && cp "$HARNESS_PREBUILT/build/$2.$e" "$B/$2.$e"
    done
    REUSED[$2]=1; NREUSED=$((NREUSED + 1)); return
  fi
  echo "== $2"
  (cd "$1" && LEAN_PATH=$B:$F/lean/build:$LP "$LEAN" -o "$B/$2.olean" "$2.lean") 2>&1 |
    grep -v "semireducible\|instance_reducible\|^definition with" || true
  [ -f "$B/$2.olean" ] || { echo "goalbuild: $2 did not build"; exit 1; }
}
NREUSED=0
build "$KL" DsvStatement
build "$KL" DsvNet
# the harness's modules present in kit/lean, in build.sh's order
mapfile -t ORDER < <(sed -n '/^MODS=(/,/^)/p' "$H/build.sh" | grep -o 'Harness/[A-Za-z0-9_/]*')
for m in "${ORDER[@]}"; do [ -f "$KL/$m.lean" ] && build "$KL" "$m"; done
# (a lookup table: `printf | grep -q` under pipefail fails at random when grep exits early)
declare -A INORDER; for m in "${ORDER[@]}"; do INORDER[$m]=1; done
for f in $(cd "$KL" && find Harness -name '*.lean' | sed 's/\.lean$//'); do
  [ -n "${INORDER[$f]:-}" ] || { echo "goalbuild: $f is not in harness/lean/build.sh"; exit 1; }
done
# the kit's own trusted files (lean.trusted_init: <root>/TrustedCode/... and the empty <root>/ManualProof/...,
# which the translation imports)
for f in $(cd "$KL" && find . -path ./Harness -prune -o \( -path '*/TrustedCode/*.lean' -o -path '*/ManualProof/*.lean' \) -print | sed 's|^\./||; s/\.lean$//' | sort); do
  build "$KL" "$f"
done
[ -n "${HARNESS_PREBUILT:-}" ] && echo "goalbuild: $NREUSED fixed modules reused from HARNESS_PREBUILT"
# Goose's output for the fork, against the fixed harness modules
(cd "$F" && HARNESS_BUILD=$B ./goose.sh) 2>&1 | grep -v "semireducible\|instance_reducible\|^definition with"
# the kit's trusted files now sit beside the translation too (goose.sh): one root per search path
for d in $(cd "$KL" && find . -mindepth 1 -maxdepth 1 -type d ! -name Harness | sed 's|^\./||'); do
  [ -d "$F/lean/build/$d" ] && rm -rf "${B:?}/$d"
done
for f in $(cd "$KL" && ls *Spec.lean *Main.lean | sed 's/\.lean$//' | sort -r); do build "$KL" "$f"; done
build "$KL" Goal
echo "== GoalCheck"
out=$(cd "$KL" && LEAN_PATH=$B:$F/lean/build:$LP "$LEAN" GoalCheck.lean 2>&1 |
  grep -v "semireducible\|instance_reducible\|^definition with")
echo "$out" | grep -qE "(^|: )error:" && { echo "$out"; echo "goalbuild: GoalCheck failed"; exit 1; }
echo "$out" | tr '\n' ' ' | grep -o "'dsv_goal_check[a-z_]*' depends on axioms: \[[^]]*\]" |
  sed 's/depends on axioms: \[\(.\{0,60\}\).*/axioms: [\1 ...]/'
n=$(echo "$out" | grep -o "Perennial\.[A-Za-z_.]*" | sort -u | wc -l)
echo "goalbuild: GoalCheck elaborates; $(echo "$out" | grep -c sorryAx) theorem(s) depend on sorryAx; $n distinct Perennial axioms"
