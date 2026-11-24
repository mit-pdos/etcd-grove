#!/bin/bash
# goal-check.sh PROJECT GOALDIR: is the challenge run's project (its checkout, with the built Lake
# packages) "done" as the challenge defines it? GOALDIR is the run's goal directory (runs/RUN/goal,
# copied beside the checkout as .goal by sandbox.sh verify): lab/ (the export's DIR.lab), CHALLENGE.txt,
# and `challenge` (commit=: the challenge commit). verify.sh runs it in the check view, after the
# comparator.
# "Done" is the challenge's own (the skill's CHALLENGE.md, "Done"; the challenge's CLAUDE.md, "The goal"),
# from the project's HEAD:
#   1. the fixed files (CLAUDE.md's "Do not edit" list) and the environment (Net/, Robustness/, GooseLang/,
#      examples/lib/, models/, the main tree's Spec/ and Proof/, etc/ but the kit file and its prophecy
#      patches; the lakefile, manifest and toolchain) are the challenge commit's, byte for byte;
#   2. `lake build` of the goal's module succeeds;
#   3. `#print axioms` of the goal: Lean's three (propext, Classical.choice, Quot.sound), nothing else;
#   4. the non-vacuity module builds, if CLAUDE.md names one; the kitlibs-check (etc/kitlibs-check.py,
#      or its old name etc/premcheck.py) accepts, if the challenge has one;
#   5. every check CLAUDE.md lists passes (run from the project, whose etc/ step 1 holds to the export's).
# One PASS/FAIL line per check; exit 1 on a FAIL.
P=${1:?usage: goal-check.sh PROJECT GOALDIR}; G=${2:?usage: goal-check.sh PROJECT GOALDIR}
G=$(cd "$G" && pwd) || exit 1
cd "$P" || exit 1
fail=0
[ -f "$G/challenge" ] || { echo "FAIL no $G/challenge (not a challenge run's goal directory)"; exit 1; }

challenge_done() {
    local cc kit conf thm sol fixed c t out
    cc=$(sed -n 's/^commit=//p' "$G/challenge"); kit=$(sed -n 's/^kit: //p' "$G/CHALLENGE.txt")
    conf=$G/lab/comparator/challenge.conf
    thm=$(sed -n 's/^theorem=//p' "$conf"); sol=$(sed -n 's/^solution=//p' "$conf")
    g() { git -c safe.directory='*' "$@"; }
    g cat-file -e "$cc^{commit}" 2>/dev/null || { echo "FAIL the project does not have the challenge commit ${cc:0:9}"; return 1; }
    # 1. what the challenge fixes (from the challenge commit's own CLAUDE.md)
    fixed=$(g show "$cc:CLAUDE.md" | sed -n '/^## Do not edit/,/^## /p' | sed -n 's/^- `\([^` ]*\.lean\)`$/\1/p')
    [ -n "$fixed" ] || { echo "FAIL no fixed files in the challenge's CLAUDE.md"; fail=1; }
    local env=(Net Robustness GooseLang examples/lib models Spec Proof etc lakefile.toml lake-manifest.json lean-toolchain
               ":(exclude)etc/dsv/$kit.py" ":(exclude)etc/proph-patches/dsv-$kit")
    out=$(g diff --name-only "$cc" HEAD -- $fixed "${env[@]}"; g status --porcelain --untracked-files=no -- $fixed "${env[@]}")
    if [ -z "$out" ]; then echo "PASS the $(echo "$fixed" | wc -w) fixed files and the environment are the challenge's (${cc:0:9})"
    else echo "FAIL changed since the challenge (fixed files or the environment):"; echo "$out" | sort -u | head -15 | sed 's/^/  /'; fail=1; fi
    if [ -n "$(g diff --name-only "$cc" HEAD -- "etc/dsv/$kit.py")" ]; then
        echo "NOTE etc/dsv/$kit.py changed (its statement and premise parts must not: the checks below compare the generated statement)"
    fi
    # 2. the goal builds
    if lake build "$sol" >"${TMPDIR:-/tmp}/goal-build.log" 2>&1; then echo "PASS lake build $sol"
    else echo "FAIL lake build $sol"; grep -E 'error' "${TMPDIR:-/tmp}/goal-build.log" | head -10; fail=1; fi
    # 3. its axioms
    t=$(mktemp -d); printf 'import %s\n#print axioms %s\n' "$sol" "$thm" >"$t/Ax.lean"
    out=$(lake env lean "$t/Ax.lean" 2>&1); rm -rf "$t"; echo "$out" | sed 's/^/  /' | head -10
    local ax; ax=$(echo "$out" | tr -d '\n' | sed -n "s/.*depends on axioms: \[\([^]]*\)\].*/\1/p" | tr ',' '\n' | sed 's/ //g' | grep -v '^$' | sort)
    if echo "$out" | grep -q "does not depend on any axioms"; then echo "PASS $thm depends on no axioms"
    elif [ -n "$ax" ] && [ -z "$(echo "$ax" | grep -vxE 'propext|Classical.choice|Quot.sound')" ]; then
        echo "PASS $thm depends on Lean's axioms only: $(echo $ax)"
    else echo "FAIL $thm's axioms: $(echo $ax) (only propext, Classical.choice, Quot.sound are allowed)"; fail=1; fi
    # 4. non-vacuity, kitlibs-check
    local nv; nv=$(g show "$cc:CLAUDE.md" | sed -n 's/.*the non-vacuity module builds: `\([^`]*\)`.*/\1/p' | head -1)
    if [ -n "$nv" ]; then
        if lake build "$nv" >/dev/null 2>&1; then echo "PASS the non-vacuity module $nv builds"; else echo "FAIL the non-vacuity module $nv"; fail=1; fi
    else echo "SKIP no non-vacuity module (the statement has no premises)"; fi
    local kc="" kconf=""
    for c in etc/kitlibs-check.py etc/premcheck.py; do g cat-file -e "$cc:$c" 2>/dev/null && { kc=$c; break; }; done
    for c in "etc/dsv/$kit-kitlibs-check.conf" "etc/dsv/$kit-premcheck.conf"; do g cat-file -e "$cc:$c" 2>/dev/null && { kconf=$c; break; }; done
    if [ -n "$kc" ] && [ -n "$kconf" ]; then
        if python3 "$kc" "$kconf" >"${TMPDIR:-/tmp}/kitlibs.log" 2>&1; then echo "PASS $kc $kconf"; else echo "FAIL $kc $kconf"; tail -10 "${TMPDIR:-/tmp}/kitlibs.log"; fail=1; fi
    else echo "SKIP no kitlibs-check in this challenge"; fi
    # 5. the challenge's checks
    while read -r c; do
        [ -n "$c" ] || continue
        if (timeout 3600 bash -c "$c") >"${TMPDIR:-/tmp}/check.log" 2>&1; then echo "PASS $c"
        else echo "FAIL $c"; tail -8 "${TMPDIR:-/tmp}/check.log" | sed 's/^/  /'; fail=1; fi
    done < <(g show "$cc:CLAUDE.md" | sed -n '/^- The checks/,/^$/p' | sed -n 's/^ *- `\(.*\)`$/\1/p')
    return $fail
}
challenge_done; exit $?
