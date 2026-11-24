#!/bin/bash
# comparator-check.sh PROJECT GOALDIR: does the challenge run's project prove the challenge's goal, by
# the comparator (leanprover/comparator)? Lab-side only: verify.sh runs it in the check view, with the
# tools mounted from cache/tools/comparator (comparator-tools.sh).
# The comparator step runs before any of the project's Lean code is compiled outside its sandbox
# (verify.sh), as its README requires; this script's own environment is fresh (HOME, git config) and
# takes nothing from the run's home but the toolchain, which is mounted read-only.
# Prints PASS/FAIL lines; exit 1 on a FAIL. Env: CMP_TOOLS (/opt/lab/comparator), LEAN_TC (the
# toolchain directory; default the elan toolchain the lab's OFFLINE.txt names), CMP_WORK (W; default a
# fresh temporary directory), LAKEPKGS, CMP_RECORD (below).
P=$(cd "${1:?usage: comparator-check.sh PROJECT GOALDIR}" && pwd) || exit 1
G=$(cd "${2:?usage: comparator-check.sh PROJECT GOALDIR}" && pwd) || exit 1
CMP=${CMP_TOOLS:-/opt/lab/comparator}
TC=${LEAN_TC:-$HOME/.elan/toolchains/$(sed -n 's#^lean-toolchain: leanprover/lean4:#leanprover--lean4---#p' "$G/lab/OFFLINE.txt")}
t0=$SECONDS
fail() { echo "FAIL $*"; exit 1; }
note() { echo "  [$((SECONDS - t0))s] $*"; }

# GOALDIR is runs/RUN/goal of a challenge run (sandbox.sh new --challenge): lab/ (the export's DIR.lab:
# comparator/challenge.conf with `tree=etcd-grove COMMIT` and `statement=MODULE`, comparator/Challenge.lean,
# OFFLINE.txt, MANIFEST.txt), CHALLENGE.txt, and `challenge` (commit=: the work tree's initial commit,
# the challenge as exported). The challenge is that commit, not Goose's output regenerated: in a fresh
# workspace W (`git archive` of the commit; the Lake packages from LAKEPKGS, default the project's
# .lake/packages, checked against the manifest's pins):
#   1. the lab's challenge module DsvChallenge (Challenge.lean: the goal, its proof a `sorry`, over the
#      exported statement module) is added (a lean_lib of its own) and built, from the exported files
#      only, before any file of the solution is in W;
#   2. the solution's agent-owned files are copied in: the files the project's HEAD adds, changes or
#      deletes since the challenge commit under the kit's Lean trees, Dsverify/{Spec,Proof,Code,
#      GeneratedProof}/<the kit's Go module path>; nothing else (a change elsewhere is listed and left out).
#      Refused: a change to a fixed file (the challenge's CLAUDE.md, "Do not edit") or to any module of
#      the statement's import closure (the statement would then be about something else), with one
#      exception: the KitLibs file, when the challenge has a kitlibs-check (etc/kitlibs-check.py, or
#      its old name etc/premcheck.py), which is copied in before step 1 (it is part of the statement);
#   3. the comparator: the solution's goal module built in its sandbox, both exported, the theorem's
#      statement compared constant by constant, the axioms limited to Lean's three (CHALLENGE.md,
#      "Done"), the proof replayed by Lean's kernel and nanoda's;
#   4. if the challenge has a kitlibs-check: run after the comparator (it builds the solution's
#      non-vacuity module), with the exported copies of its script and configuration, in landrun; its
#      verdict and the instance's axioms it lists are recorded (the goal itself may use none of them).
# Results: PASS/FAIL lines, a `RESULT {json}` line, and W/result.json (with CMP_RECORD=DIR, the logs and
# result.json are copied to DIR).
tree_mode() {
    local CL=$G/lab/comparator TCONF=$G/lab/comparator/challenge.conf
    tconf() { sed -n "s/^$1=//p" "$TCONF" | head -1; }
    local thm sol stmt gomod tree cc kit
    thm=$(tconf theorem); sol=$(tconf solution); stmt=$(tconf statement); gomod=$(tconf gomodule); tree=$(tconf tree)
    for v in thm sol stmt gomod tree; do [ -n "${!v}" ] || fail "$TCONF: no ${v}"; done
    cc=$(sed -n 's/^commit=//p' "$G/challenge" 2>/dev/null); [ -n "$cc" ] || fail "$G/challenge: no commit="
    kit=$(sed -n 's/^kit: //p' "$G/CHALLENGE.txt"); [ -n "$kit" ] || fail "$G/CHALLENGE.txt: no kit"
    for x in "$CMP/bin/comparator" "$CMP/bin/lean4export" "$CMP/bin/landrun" "$TC/bin/lake"; do
        [ -x "$x" ] || fail "no $x"
    done
    W=${CMP_WORK:-$(mktemp -d)}; mkdir -p "$W"; L=$W/logs; mkdir -p "$L"
    export HOME=$W/home; mkdir -p "$HOME"
    # git's config is HOME's: the comparator's sandbox passes only PATH and HOME, and Lake there runs
    # git on every package (a git that refuses a repository, e.g. for its owner, reads as "URL has
    # changed", and Lake deletes the package and clones it again, offline)
    export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=$HOME/.gitconfig
    git config --file "$HOME/.gitconfig" safe.directory '*'
    export PATH=$TC/bin:$CMP/bin:/usr/local/go/bin:/usr/bin:/bin
    unset LEAN_PATH LEAN_SRC_PATH ELAN_HOME
    export COMPARATOR_LANDRUN=$CMP/bin/landrun COMPARATOR_LEAN4EXPORT=$CMP/bin/lean4export
    g() { git -C "$1" "${@:2}"; }

    # the solution: the project's HEAD, descended from the challenge commit
    local psha; psha=$(g "$P" rev-parse HEAD) || fail "the project is not a git checkout"
    [ -z "$(g "$P" status --porcelain --untracked-files=no)" ] || fail "the project's checkout has changes"
    g "$P" cat-file -e "$cc^{commit}" 2>/dev/null || fail "the project does not have the challenge commit ${cc:0:9}"
    g "$P" merge-base --is-ancestor "$cc" HEAD || fail "the project's HEAD does not descend from the challenge commit ${cc:0:9}"

    # the challenge, from its commit (content-addressed: the tree as exported)
    local WS=$W/ws; mkdir -p "$WS"
    g "$P" archive "$cc" | tar -x -C "$WS" || fail "git archive of the challenge commit"
    cmp -s "$WS/CHALLENGE.txt" "$G/CHALLENGE.txt" || fail "the challenge commit's CHALLENGE.txt is not the run's"
    [ "$(sed -n 's/^source: \([0-9a-f]*\).*/\1/p' "$G/CHALLENGE.txt")" = "${tree#etcd-grove }" ] ||
        fail "challenge.conf's tree= is not CHALLENGE.txt's source"
    [ -f "$WS/lakefile.toml" ] && [ ! -e "$WS/lakefile.lean" ] || fail "the challenge's lakefile is not lakefile.toml alone"
    for n in DsvChallenge; do [ -e "$WS/$n.lean" ] || [ -e "$WS/$n" ] && fail "the challenge has $n, a name the check reserves"; done
    local LP=${LAKEPKGS:-$P/.lake/packages}
    [ -d "$LP" ] || fail "no Lake packages at $LP (LAKEPKGS)"
    # (W's own: as root, cp -a keeps the packages' owner, another user's)
    mkdir -p "$WS/.lake"; cp -a "$LP" "$WS/.lake/packages"; chmod -R u+w "$WS/.lake/packages"
    chown -R "$(id -u):$(id -g)" "$WS/.lake/packages"
    python3 -I - "$WS/lake-manifest.json" "$WS/.lake/packages" <<'EOF' || fail "the Lake packages are not at the challenge's pins"
import json, subprocess, sys
for p in json.load(open(sys.argv[1]))["packages"]:
    d = f'{sys.argv[2]}/{p["name"]}'
    h = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if h != p["rev"]: print(f"  {p['name']}: {h[:12]}, not {p['rev'][:12]}"); sys.exit(1)
EOF
    echo "PASS the challenge: commit ${cc:0:9} (etcd-grove ${tree#etcd-grove }; kit $kit); solution ${psha:0:9}; packages at the manifest's pins"

    # the kitlibs-check, if the challenge has one (renamed from premcheck; either name)
    local kc="" kconf="" kfile=""
    for s in etc/kitlibs-check.py etc/premcheck.py; do [ -f "$WS/$s" ] && { kc=$s; break; }; done
    for s in "etc/dsv/$kit-kitlibs-check.conf" "etc/dsv/$kit-premcheck.conf"; do [ -f "$WS/$s" ] && { kconf=$s; break; }; done
    if [ -n "$kc" ] && [ -n "$kconf" ]; then
        kfile=$(sed -n 's/^kitlibs_file *= *//p' "$WS/$kconf" | head -1)
        [ -n "$kfile" ] || fail "$kconf: no kitlibs_file="
    else kc=""; fi

    # the solution's changes, classified (python: the statement's closure from the exported Lean)
    local root; root=$(echo "$gomod" | awk -F/ '{for (i=1; i<=NF; i++) {gsub(/[.-]/, "_", $i); printf "%s%s", (i>1 ? "/" : ""), $i}}')
    g "$P" diff --name-status --no-renames "$cc" HEAD >"$L/diff.txt"
    python3 -I - "$WS" "$stmt" "$root" "$L/diff.txt" "$kfile" "$W/plan.txt" <<'EOF' >"$L/plan.log" 2>&1 || { cat "$L/plan.log"; fail "the solution changes files the check cannot accept"; }
import os, re, sys
WS, stmt, root, diff, kfile, out = sys.argv[1:]
IMP = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', re.M)
def path(m): return m.replace(".", "/") + ".lean"
seen, todo = set(), [stmt]
while todo:
    m = todo.pop()
    if m in seen or not os.path.exists(os.path.join(WS, path(m))): continue
    seen.add(m)
    todo += IMP.findall(open(os.path.join(WS, path(m)), errors="replace").read())
closure = {path(m) for m in seen}
# the fixed files: the challenge's CLAUDE.md, "Do not edit", one "- `path`" per file
fixed, on = set(), False
for l in open(os.path.join(WS, "CLAUDE.md")):
    if l.startswith("## "): on = l.strip() == "## Do not edit"
    mt = re.match(r"- `([^`\s]+\.lean)`$", l.strip())
    if on and mt: fixed.add(mt.group(1))
own = re.compile(r"^Dsverify/(Spec|Proof|Code|GeneratedProof)/" + re.escape(root) + r"(/.*)?\.lean$")
take, left, bad = [], [], []
for l in open(diff):
    st, f = l.rstrip("\n").split("\t", 1)
    if f in fixed: bad.append(f"{f}: a fixed file ({st})")
    elif own.match(f):
        if f in closure and f != kfile: bad.append(f"{f}: in the statement's import closure ({st})")
        else: take.append(f"{st} {f}")
    else: left.append(f"{st} {f}")
print(f"statement closure: {len(closure)} modules; fixed files: {len(fixed)}; kit Lean root: {root}")
for x in left: print(f"left out (not agent-owned Lean): {x}")
for x in bad: print(f"REFUSED {x}")
if kfile and not any(t.endswith(" " + kfile) for t in take): print(f"note: the solution does not change {kfile}")
open(out, "w").write("".join(t + "\n" for t in take))
sys.exit(1 if bad else 0)
EOF
    grep -v '^left out' "$L/plan.log" | sed 's/^/  /'
    echo "  taken from the solution: $(wc -l <"$W/plan.txt") files; left out: $(grep -c '^left out' "$L/plan.log") (list: $L/plan.log)"
    # the KitLibs file is part of the statement: in before the challenge is built; its imports must be
    # the challenge's (no new module)
    if [ -n "$kfile" ] && grep -q " $kfile\$" "$W/plan.txt"; then
        g "$P" show "HEAD:$kfile" >"$WS/$kfile" || fail "the solution's $kfile"
        local i; for i in $(sed -nE 's/^\s*(public\s+|private\s+)?(meta\s+)?import\s+(all\s+)?([A-Za-z0-9_.]+).*/\4/p' "$WS/$kfile"); do
            f=$(echo "$i" | tr . /).lean
            if [ -f "$WS/$f" ] || [ -n "$(find "$WS/.lake/packages" -path "*/$f" -print -quit)" ]; then :
            else fail "$kfile imports $i, not a module of the challenge"; fi
            grep -q " $f\$" "$W/plan.txt" && fail "$kfile imports $i, a module of the solution"
        done
        echo "  $kfile: the solution's (part of the statement; imports only the challenge's modules)"
    fi

    # 1. the challenge module, built before any other file of the solution is in W
    cp "$CL/Challenge.lean" "$WS/DsvChallenge.lean"
    printf '\n# the lab'"'"'s challenge module (comparator-check.sh)\n[[lean_lib]]\nname = "DsvChallenge"\n' >>"$WS/lakefile.toml"
    (cd "$WS" && lake build DsvChallenge) >"$L/challenge.log" 2>&1 \
        || { grep -E "error" "$L/challenge.log" | head -10; fail "the challenge does not build"; }
    note "challenge built ($(grep -oE '[0-9]+ jobs' "$L/challenge.log" | tail -1))"

    # 2. the solution's files
    local st f
    while read -r st f; do
        [ -n "$f" ] || continue
        if [ "$f" = "$kfile" ]; then continue; fi
        if [ "$st" = D ]; then rm -f "$WS/$f"
        else mkdir -p "$WS/$(dirname "$f")"; g "$P" show "HEAD:$f" >"$WS/$f" || fail "git show HEAD:$f"; fi
    done <"$W/plan.txt"

    # 3. the comparator
    local kernels='{}'
    [ -x "$CMP/bin/nanoda_bin" ] && kernels="{\"nanoda\": [\"$CMP/bin/nanoda_bin\"]}"
    python3 -I - "$WS/config.json" "$thm" "$sol" "$kernels" <<'EOF'
import json, sys
out, thm, sol, kernels = sys.argv[1:]
json.dump({"challenge_module": "DsvChallenge", "solution_module": sol, "theorem_names": [thm],
           "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
           "external_kernels": json.loads(kernels)}, open(out, "w"), indent=1)
EOF
    (cd "$WS" && lake env comparator config.json) >"$L/comparator.log" 2>&1; local rc=$?
    grep -E '^(Building|Exporting|Running|Lean |nanoda|Quotient|Your|uncaught|Error|error:|Illegal|Const|Challenge|Solution|Child)' \
        "$L/comparator.log" | cut -c1-200 | tail -20 | sed 's/^/  /'
    note "comparator done (exit $rc)"
    local ok=false
    if [ $rc = 0 ] && grep -q "Your solution is okay!" "$L/comparator.log"; then ok=true
        echo "PASS the comparator: $thm has the exported statement, uses only Lean's three axioms, and the kernel accepts it on replay$([ "$kernels" != '{}' ] && echo ' (Lean and nanoda)')"
    else echo "FAIL the comparator rejects $thm (log: $L/comparator.log)"; fi

    # 4. the kitlibs-check (after the comparator: it compiles the solution's non-vacuity module)
    local kv=none
    if [ -n "$kc" ]; then
        if (cd "$WS" && "$CMP/bin/landrun" --best-effort --ro / --rw /dev --rwx "$WS" --rwx "$HOME" --rwx /tmp \
                --env PATH --env HOME -- python3 "$kc" "$kconf") >"$L/kitlibs-check.log" 2>&1; then
            kv=accepted; echo "PASS kitlibs-check ($kc $kconf): accepted"
        else kv=refused; echo "FAIL kitlibs-check ($kc $kconf): refused (log: $L/kitlibs-check.log)"; ok=false; fi
        grep -E '^(field|axiom|instance|ACCEPTED|REFUSED)' "$L/kitlibs-check.log" | head -40 | sed 's/^/  /'
    else echo "SKIP no kitlibs-check in this challenge"; fi

    python3 -I - "$W/result.json" "$kit" "$tree" "$cc" "$psha" "$thm" "$ok" "$kv" "$(wc -l <"$W/plan.txt")" \
        "$([ "$kernels" != '{}' ] && echo nanoda)" <<'EOF'
import json, sys
o, kit, tree, cc, ps, thm, ok, kv, n, k = sys.argv[1:]
r = {"kit": kit, "statement": tree, "challenge_commit": cc, "solution": ps, "theorem": thm,
     "comparator": ok == "true", "axioms": ["propext", "Quot.sound", "Classical.choice"],
     "kernels": ["lean"] + ([k] if k else []), "kitlibs_check": kv, "solution_files": int(n)}
json.dump(r, open(o, "w")); print("RESULT " + json.dumps(r))
EOF
    if [ -n "${CMP_RECORD:-}" ]; then mkdir -p "$CMP_RECORD" && cp -r "$L" "$W/result.json" "$W/plan.txt" "$CMP_RECORD/"; fi
    [ "$ok" = true ] || exit 1
    exit 0
}
[ -f "$G/lab/comparator/challenge.conf" ] && grep -q '^tree=' "$G/lab/comparator/challenge.conf" ||
    fail "$G/lab/comparator/challenge.conf: no tree= (not an exported challenge's)"
tree_mode
