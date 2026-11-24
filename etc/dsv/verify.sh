#!/bin/bash
# Run inside a check view (sandbox.sh verify RUN TAG puts it there): rebuild a challenge run's result
# from a fresh checkout and check it. PROJECT is that checkout: the run's work tree (the challenge's
# repository) at TAG, with the built Lake packages in .lake/packages and the lab's files beside it in
# /home/agent/work/.goal (runs/RUN/goal: the export's DIR.lab, CHALLENGE.txt, the challenge commit).
#   1. HEAD descends from the challenge commit
#   2. the goal, by the comparator (comparator-check.sh, its tree= mode), ahead of any build of the
#      project's Lean outside the comparator's sandbox
#   3. "done" as the challenge defines it (the skill's CHALLENGE.md, its CLAUDE.md): goal-check.sh
# One "PASS"/"FAIL" line per step, the last "verified" or "NOT verified"; exit 1 on a FAIL.
P=${1:?usage: verify.sh PROJECT}; cd "$P" || exit 1
# the container's console is a terminal: without this, git log waits in a pager for a key
export GIT_PAGER=cat PAGER=cat
fail=0; t0=$SECONDS
step() { echo; echo "== $* ($((SECONDS - t0))s)"; }
ok() { echo "PASS $*"; }
bad() { echo "FAIL $*"; fail=1; }
TMP=$(mktemp -d /home/agent/tmp/verify.XXXXXX)
GOAL=/home/agent/work/.goal
[ -f "$GOAL/challenge" ] || { echo "FAIL no $GOAL/challenge (not a challenge run's checkout)"; exit 1; }

step "checkout"
git log --oneline -1 --decorate
# (the checkout has the built packages in .lake/packages, and nothing else there)
[ -z "$(ls -A .lake | grep -v "^packages$")" ] || bad ".lake holds more than the built packages"

# Go's module and build caches fresh, in TMP: the check view's home is the throwaway run's, whose
# module cache may hold another proxy's copy of a module at the same version (go then fails the
# challenge's go.sum)
export GOMODCACHE=$TMP/gomod GOCACHE=$TMP/gocache GOFLAGS=-modcacherw XDG_CONFIG_HOME=$TMP/config
step "the challenge"
sed 's/^/  /' "$GOAL/CHALLENGE.txt"
cc=$(sed -n 's/^commit=//p' "$GOAL/challenge")
if git merge-base --is-ancestor "$cc" HEAD 2>/dev/null; then ok "HEAD descends from the challenge commit ${cc:0:9} ($(git rev-list --count "$cc..HEAD") commits)"
else bad "HEAD does not descend from the challenge commit ${cc:0:9}"; fi
step "the goal, by the comparator (tree= mode)"
if LAKEPKGS="$P/.lake/packages" bash /opt/lab/comparator-check.sh "$P" "$GOAL"; then ok "goal, by the comparator"; else bad "goal, by the comparator"; fi
step "done, as the challenge defines it (goal-check.sh)"
if bash /opt/lab/goal-check.sh "$P" "$GOAL"; then ok "done"; else bad "not done"; fi
chmod -R u+w "$TMP" 2>/dev/null; rm -rf "$TMP"
step "$([ $fail = 0 ] && echo "verified" || echo "NOT verified")"
exit $fail
