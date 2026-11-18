#!/bin/bash
# challenge/check.sh NAME [SOLUTION]: the comparator's check of challenge NAME (challenge/NAME,
# its comparator.json) against the solution, this repository's checkout SOLUTION (default: the
# one this script is in), each built and exported (lean4export) in its own Lake workspace, then
# compared by the comparator's own code (tools/CompareExports.lean): every constant the theorems'
# and the permitted axioms' statements reach is the challenge's, the solution's theorems use no
# axiom but the permitted ones, and Lean's kernel accepts the solution's export on replay.
#
# The tools (leanprover/comparator and leanprover/lean4export v4.34.0, compiled with this
# repository's toolchain, and compare-exports) are fetched and built into challenge/.tools once.
# The solution must be built up to date (`lake build MODULE`): this script never builds it (it
# runs `lake build --no-build`), so it never writes into the solution's checkout.
# Env: TOOLS (default challenge/.tools), WORK (exports; default a fresh temporary directory).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
name=${1:?usage: challenge/check.sh NAME [SOLUTION]}
C=$here/$name; S=$(cd "${2:-$here/..}" && pwd)
TOOLS=${TOOLS:-$here/.tools}; WORK=${WORK:-$(mktemp -d)}
TAG=v4.34.0
cfg=$C/comparator.json
[ -f "$cfg" ] || { echo "FAIL no $cfg"; exit 1; }
tc=$(cat "$S/lean-toolchain")
[ "$(cat "$C/lean-toolchain")" = "$tc" ] || { echo "FAIL the challenge's toolchain is not the solution's ($tc)"; exit 1; }

# the tools
cmp=$TOOLS/comparator; exp=$cmp/.lake/packages/lean4export
if [ ! -x "$cmp/.lake/build/bin/compare-exports" ] || [ ! -x "$exp/.lake/build/bin/lean4export" ]; then
    echo "building the comparator's tools ($TAG, $tc) in $TOOLS"
    rm -rf "$cmp"; mkdir -p "$cmp"
    curl -sSfL "https://codeload.github.com/leanprover/comparator/tar.gz/refs/tags/$TAG" | tar xz -C "$cmp" --strip-components=1
    echo "$tc" >"$cmp/lean-toolchain"
    cp "$here/tools/CompareExports.lean" "$cmp/"
    printf '\n[[lean_exe]]\nname = "compare-exports"\nroot = "CompareExports"\n' >>"$cmp/lakefile.toml"
    (cd "$cmp" && lake build compare-exports) >"$WORK/tools.log" 2>&1 || { tail -20 "$WORK/tools.log"; exit 1; }
    echo "$tc" >"$exp/lean-toolchain"
    (cd "$exp" && lake build) >>"$WORK/tools.log" 2>&1 || { tail -20 "$WORK/tools.log"; exit 1; }
fi

# the export targets: Main.lean's builtinTargets ++ theorem_names ++ permitted_axioms ++ primitiveTargets
mapfile -t targets < <(python3 -I - "$cfg" <<'EOF'
import json, sys
c = json.load(open(sys.argv[1]))
builtin = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if "Quot.sound" in c["permitted_axioms"] else []
prim = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq",
        "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
        "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk", "Char",
        "optParam", "autoParam", "semiOutParam", "outParam"]
for n in builtin + c["theorem_names"] + c["permitted_axioms"] + prim:
    print(n)
EOF
)
module() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' "$cfg" "$1"; }
cmod=$(module challenge_module); smod=$(module solution_module)

echo "building the challenge ($cmod) in $C"
(cd "$C" && lake build "$cmod") >"$WORK/challenge-build.log" 2>&1 || { grep -E '^error' "$WORK/challenge-build.log" | head; echo "FAIL the challenge does not build"; exit 1; }
echo "checking the solution ($smod) in $S is built"
(cd "$S" && lake build --no-build "$smod") >"$WORK/solution-build.log" 2>&1 || { tail -3 "$WORK/solution-build.log"; echo "FAIL the solution is not built (lake build $smod in $S)"; exit 1; }

echo "exporting ${#targets[@]} targets from each"
(cd "$C" && lake env "$exp/.lake/build/bin/lean4export" "$cmod" -- "${targets[@]}") >"$WORK/challenge.ndjson"
(cd "$S" && lake env "$exp/.lake/build/bin/lean4export" "$smod" -- "${targets[@]}") >"$WORK/solution.ndjson"
ls -la "$WORK"/*.ndjson | awk '{print "  " $5 " bytes " $NF}'

"$cmp/.lake/build/bin/compare-exports" "$cfg" "$WORK/challenge.ndjson" "$WORK/solution.ndjson"
