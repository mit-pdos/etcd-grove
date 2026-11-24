#!/bin/bash
# Run inside a run's check view (sandbox.sh start-shell RUN bash /opt/lab/check-env.sh):
# what the agent can and cannot reach. Each line PASS or FAIL; exit 1 on a FAIL.
# Uses /home/agent/tmp/check (removed at the end).
#   check-env.sh              the generic checks: isolation, the proxy, the tools (run.sh runs them in
#                             the throwaway run test1)
#   check-env.sh --challenge  a challenge run's own view (sandbox.sh new --challenge; run.sh runs it
#                             in the run, after the generic checks): isolation, the leak checks of the
#                             exported tree against the lab's copy of the export's MANIFEST.txt (mounted
#                             at /opt/lab/goal in check views only), and its offline needs (OFFLINE.txt)
fail=0
CHALLENGE=; [ "${1:-}" = --challenge ] && CHALLENGE=1
# pkg_imports MODULE (in a Lean tree): the package modules (Perennial, Iris, Batteries, Qq) its import
# closure within the tree imports
pkg_imports() {
    python3 -I - "$1" <<'PYEOF'
import os, re, sys
IMP = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', re.M)
seen, todo, pk = set(), [sys.argv[1]], set()
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m); f = m.replace(".", "/") + ".lean"
    if not os.path.exists(f):
        pk.add(m); continue
    todo += IMP.findall(open(f, errors="replace").read())
print(" ".join(sorted(m for m in pk if m.split(".")[0] in ("Perennial", "Iris", "Batteries", "Qq"))))
PYEOF
}
ok() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
step() { echo "  ... $*"; }   # before a slow step
# the names the leak checks look for: etcd-grove's, and the people of /opt/lab/leak-names.txt (etc/dsv's,
# its `person` lines; mounted in check views only), as one Perl regular expression
NAMES='etcd-grove|grove-etcd|etcd_grove'
PEOPLE=$( [ -r /opt/lab/leak-names.txt ] && awk -F'\t' '$1 == "person" {print $2}' /opt/lab/leak-names.txt | paste -sd'|')
[ -n "$PEOPLE" ] && NAMES="$NAMES|$PEOPLE"
[ -n "$PEOPLE" ] || echo "NOTE no /opt/lab/leak-names.txt: the leak checks look for etcd-grove's names only"
T=/home/agent/tmp/check; rm -rf "$T"; mkdir -p "$T"; cd "$T"

# isolation: none of the host's trees
for p in /root/.claude /root/.elan /var/lib/machines /etc/ssh /etc/shadow; do
    [ -e "$p" ] && bad "visible: $p" || ok "not visible: $p"
done
hits=$(ls -d /root/.claude* /home/*/.claude-* 2>/dev/null | head -3)
[ -z "$hits" ] && ok "no other Claude config dirs" || bad "visible: $hits"
if ls /root 2>/dev/null | grep -q .; then bad "/root not empty"; else ok "/root empty or absent"; fi
# .lake: Lake's package clones (from the mirrors; Perennial's own docs mention etcd-grove) and build
# outputs, which a continued run inherits, are searched too
# (the check-only scripts, mounted in check views alone, name it; a challenge's work tree and
# skill are etcd-grove's by design: checked apart, below)
# A match inside one of leak-names.txt's allow-list patterns that hold for every file (an empty
# PATH-RE: the public forks' Go module paths, which the module cache at /opt/goproxy holds) is not a
# leak, as in kitgen's leak check
hits=$(grep -rIlZ -i -P "$NAMES" /etc /opt /home/agent --exclude-dir=mirrors --exclude-dir=tmp --exclude-dir=.lake --exclude=check-env.sh --exclude=verify.sh --exclude=goal-check.sh --exclude=comparator-check.sh --exclude=leak-names.txt ${CHALLENGE:+--exclude-dir=work --exclude-dir=goal --exclude-dir=skills} 2>/dev/null |
    python3 -I -c '
import re, sys
names = re.compile(sys.argv[1], re.I)
allow = [re.compile(l.rstrip("\n").split("\t")[2]) for l in open(sys.argv[2])
         if l.startswith("allow\t") and l.split("\t")[1] == ""] if sys.argv[2] else []
for f in sys.stdin.buffer.read().split(b"\0"):
    if not f: continue
    for line in open(f, errors="replace"):
        spans = [a.span() for r in allow for a in r.finditer(line)]
        if any(not any(s <= m.start() and m.end() <= e for s, e in spans) for m in names.finditer(line)):
            print(f.decode(errors="replace")); break
' "$NAMES" "$([ -r /opt/lab/leak-names.txt ] && echo /opt/lab/leak-names.txt)" | head -5)
[ -z "$hits" ] && ok "no etcd-grove or user names in /etc, /opt, /home/agent${CHALLENGE:+ (outside the work tree of the challenge)}" || bad "names found: $hits"
# proofs kept for reference and marked DSV-LAB-EXAMPLES-NOT-FOR-RUNS (in a README or SOURCE.md):
# never in a run's view (.lake included: a continued run's inherited packages)
hits=$(grep -rIl -F 'DSV-LAB-EXAMPLES-NOT-FOR-RUNS' /etc /opt /home/agent --exclude-dir=mirrors --exclude-dir=tmp --exclude=check-env.sh 2>/dev/null | head -5)
[ -z "$hits" ] && ok "no checked-in lab proofs (examples/) in /etc, /opt, /home/agent" || bad "lab examples visible: $hits"
hits=$(env | grep -i -P "etcd|grove|ANTHROPIC_API_KEY${PEOPLE:+|$PEOPLE}" | cut -d= -f1)
[ -z "$hits" ] && ok "no telling environment variables" || bad "environment: $hits"

# network: nothing but the proxy, and the proxy only to the API
python3 - <<'EOF' && ok "direct connections fail" || bad "a direct connection succeeded"
import socket, sys
for h in [("140.82.112.3", 443), ("8.8.8.8", 53), ("1.1.1.1", 443)]:
    try:
        socket.create_connection(h, timeout=3); sys.exit(1)
    except OSError:
        pass
EOF
if [ -S /run/lab/proxy.sock ] && (exec 3<>/dev/tcp/127.0.0.1/3128) 2>/dev/null; then
    code=$(curl -s -o /dev/null -w '%{http_code}' --max-time 10 https://github.com/ || true)
    [ "$code" = 000 ] && ok "proxy refuses github.com" || bad "github.com reachable ($code)"
    code=$(curl -s -o /dev/null -w '%{http_code}' --max-time 10 https://api.anthropic.com/v1/models || true)
    [ "$code" != 000 ] && ok "proxy reaches api.anthropic.com (HTTP $code)" || bad "api.anthropic.com unreachable"
    code=$(curl -s -o /dev/null -w '%{http_code}' --max-time 10 https://platform.claude.com/ || true)
    [ "$code" != 000 ] && ok "proxy reaches platform.claude.com (HTTP $code)" || bad "platform.claude.com unreachable"
else
    echo "SKIP proxy checks (no proxy in this view)"
fi

if [ -n "$CHALLENGE" ]; then
    W=/home/agent/work; G=/opt/lab/goal
    [ -f "$W/CHALLENGE.txt" ] || bad "no $W/CHALLENGE.txt (not a challenge run)"
    [ -f "$G/lab/MANIFEST.txt" ] || bad "no $G/lab/MANIFEST.txt (the lab's copy of the export's files)"
    kit=$(sed -n 's/^kit: //p' "$W/CHALLENGE.txt")
    # the tree is the export: HEAD is the challenge commit's tree, nothing else is in it
    cc=$(sed -n 's/^commit=//p' "$G/challenge")
    if [ "$(git -C "$W" rev-parse HEAD 2>/dev/null)" = "$cc" ] && [ -z "$(git -C "$W" status --porcelain 2>/dev/null)" ]; then
        ok "the work tree is the challenge commit ${cc:0:9}, clean"
    else echo "NOTE the work tree is not the clean challenge commit (a resumed run?): $(git -C "$W" log --oneline -1 2>&1)"; fi
    cmp -s "$W/CHALLENGE.txt" "$G/CHALLENGE.txt" && ok "CHALLENGE.txt is the export's" || bad "CHALLENGE.txt differs from the export's"
    # leaks: the kit's proofs and other kits' left out by the export (MANIFEST.txt's `left` lines),
    # old/dsverify, notes/dsv-*.md, the kitlibs-check's (premcheck's) test tree, etcd-grove's own
    # CLAUDE.md and .claude
    # (the export rewrites two of them: CLAUDE.md, checked by its hash below, and the goal's file, a
    # stub that must be the comparator's Challenge.lean without its header comment)
    sol=$(sed -n 's/^solution=//p' "$G/lab/comparator/challenge.conf" | tr . /).lean
    if diff -q <(sed '1,/^-\/$/d' "$G/lab/comparator/Challenge.lean") "$W/$sol" >/dev/null; then ok "the goal's file is the export's stub ($sol)"
    else bad "the goal's file $sol is not the export's stub"; fi
    hits=$(sed -n 's/^left \(\S*\) .*/\1/p' "$G/lab/MANIFEST.txt" | grep -vxF -e CLAUDE.md -e "$sol" | while read -r f; do [ -e "$W/$f" ] && echo "$f"; done | head -5)
    [ -z "$hits" ] && ok "none of the $(grep -c '^left ' "$G/lab/MANIFEST.txt") files the export left out (the kit's proofs, other kits', notes) is in the tree" || bad "left out by the export, but present: $hits"
    for p in old/dsverify notes etc/premcheck-test etc/kitlibs-check-test .claude; do
        [ -e "$W/$p" ] && bad "present: $p" || ok "absent: $p"
    done
    # the experiment scripts' section of etc/dsv/README.md (the export strips it: MANIFEST.txt's
    # `left etc/dsv/README.md#...` line)
    if grep -q '^## Running an experiment on a challenge$' "$W/etc/dsv/README.md" 2>/dev/null; then
        bad "etc/dsv/README.md has the section on the experiment scripts"
    else ok "etc/dsv/README.md has no section on the experiment scripts"; fi
    hits=$(find "$W" -path "$W/.lake" -prune -o -name 'dsv-*.md' -path '*/notes/*' -print | head -3)
    [ -z "$hits" ] && ok "no notes/dsv-*.md" || bad "notes found: $hits"
    want=$(sed -n 's/^claude-md: sha256 //p' "$W/CHALLENGE.txt"); have=$(sha256sum "$W/CLAUDE.md" | cut -d' ' -f1)
    [ -n "$want" ] && [ "$want" = "$have" ] && ok "CLAUDE.md is the challenge's (sha256 ${have:0:12})" || bad "CLAUDE.md is not the challenge's (etcd-grove's own?)"
    grep -q 'Exported from etcd-grove\|This directory is a self-contained verification challenge' "$W/CLAUDE.md" || bad "CLAUDE.md is not a challenge's"
    # the skill: the export's tree, in the config dir
    sk=$(sed -n 's/^skill: \([0-9a-f]*\).*/\1/p' "$W/CHALLENGE.txt")
    if [ -n "$sk" ]; then
        t=$(mktemp -d); git init -q --bare "$t/g"
        got=$(cd /home/agent/.claude/skills/dsverify 2>/dev/null && GIT_DIR="$t/g" GIT_INDEX_FILE="$t/i" GIT_WORK_TREE=. sh -c 'git add -A && git write-tree' 2>/dev/null)
        rm -rf "$t"
        [ "$got" = "$sk" ] && ok "the skill is the export's (tree ${sk:0:12})" || bad "the skill's tree is '${got:0:12}', not the export's ${sk:0:12}"
    else
        [ -e /home/agent/.claude/skills/dsverify ] && bad "a skill is installed, but the export has none" || ok "no skill (the export has none)"
    fi
    echo "NOTE the skill names its source project in: $(grep -rIl -i -P "$NAMES" /home/agent/.claude/skills 2>/dev/null | sed 's|.*/||' | tr '\n' ' ')"
    # accepted, but recorded: the tree names its project and people (it is etcd-grove's; kitgen's own
    # leak check, at the export, refuses the names leak-names.txt does not allow)
    if [ -n "$PEOPLE" ]; then
        n=$(grep -rIl -i -P "$PEOPLE" "$W" --exclude-dir=.lake --exclude-dir=.git 2>/dev/null | wc -l)
        echo "NOTE the work tree (etcd-grove's) names people in $n files: $(grep -rIl -i -P "$PEOPLE" "$W" --exclude-dir=.lake --exclude-dir=.git 2>/dev/null | head -4 | sed "s|$W/||" | tr '\n' ' ')"
    fi

    # offline: Go (the toolchains, the kit's module), Lean (the packages built), the challenge's checks;
    # Go's module and build caches in the scratch directory (removed at the end): the check leaves the
    # run's home as the agent is to find it
    export GOMODCACHE=$T/gomod GOCACHE=$T/gocache GOFLAGS=-modcacherw XDG_CONFIG_HOME=$T/config
    step "Go: the toolchains and the kit's module, offline"
    for v in $(sed -n 's/^go-toolchain: \(go[0-9.]*\).*/\1/p' "$G/lab/OFFLINE.txt" | sort -u); do
        (cd "$T" && GOTOOLCHAIN=$v go version 2>&1 | grep -q "$v") && ok "go toolchain $v (GOTOOLCHAIN=$v, offline)" || bad "go toolchain $v"
    done
    gd=$(sed -n 's/.*its Go in `\([^`]*\)`.*/\1/p' "$W/CLAUDE.md" | head -1)   # the kit's Go module (CLAUDE.md)
    [ -n "$gd" ] || gd=examples/dsverify/$kit
    (cd "$W/$gd" && go build ./... && go vet ./...) >"$T/go.log" 2>&1 && ok "go build and vet of $gd, offline" || { bad "go build of $gd"; tail -5 "$T/go.log"; }
    git -C "$W" status --porcelain | grep -q . && { bad "the Go check changed the work tree:"; git -C "$W" status --porcelain | head -5; }
    step "Lean: the packages built (lake build --no-build of the statement's package imports)"
    stmt=$(sed -n 's/^statement=//p' "$G/lab/comparator/challenge.conf")
    pk=$(cd "$W" && pkg_imports "$stmt")
    (cd "$W" && lake build --no-build $pk) >"$T/lake.log" 2>&1 && ok "Lake packages built: $(echo $pk | wc -w) modules the statement imports are up to date" || { bad "Lake packages not built (lake build --no-build)"; tail -5 "$T/lake.log"; }
    git -C "$W" status --porcelain | grep -q . && bad "the Lean check changed the work tree"
    # the challenge's checks (CLAUDE.md), in a scratch clone (the packages shared, read as built)
    step "the challenge's checks, in a scratch clone (several minutes)"
    git clone -q "$W" "$T/c" && mkdir -p "$T/c/.lake" && ln -s "$W/.lake/packages" "$T/c/.lake/packages"
    sed -n '/^- The checks/,/^$/p' "$W/CLAUDE.md" | sed -n 's/^ *- `\(.*\)`$/\1/p' | while read -r c; do
        (cd "$T/c" && timeout 1800 bash -c "$c") >"$T/check.log" 2>&1 && echo "PASS $c" || { echo "FAIL $c"; tail -5 "$T/check.log"; }
    done | tee "$T/checks.out"
    grep -q '^FAIL' "$T/checks.out" && fail=1
    git -C "$W" status --porcelain | grep -q . && bad "the checks changed the work tree"
    cd /; chmod -R u+w "$T" 2>/dev/null; rm -rf "$T"
    exit $fail
fi

# the tools, offline. The rest of what a challenge run needs offline (OFFLINE.txt) is the run's own
# and is checked in its view by --challenge: the Go toolchains and modules (cache/gomod-challenge, from
# `sandbox.sh prefetch --challenge`; the kit's module builds), the built Lake packages (Perennial and its
# dependencies at the manifest's pins, copied in by `sandbox.sh new --challenge`; `lake build
# --no-build`), goose (built from Perennial's pin by the checks CLAUDE.md lists)
step "the tools"
v=$(lean --version 2>&1) && ok "lean runs offline: $v" || bad "lean: $v"
v=$(go version 2>&1) && ok "go runs offline: $v" || bad "go: $v"
v=$(claude --version 2>&1) && ok "claude runs: $v" || bad "claude: $v"
git clone -q https://github.com/etcd-io/etcd etcd 2>/dev/null && bad "cloned a repository with no mirror" || ok "unmirrored clone fails"
cd /; rm -rf "$T"
exit $fail
