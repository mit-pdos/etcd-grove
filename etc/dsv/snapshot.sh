#!/bin/bash
# snapshot.sh RUN (as root, DSV_LAB set; experiment.sh starts it with nohup): while RUN's container
# runs, once a minute record the agent's work tree and its other checkouts (Lean and Go sources, notes,
# configs) as a commit of runs/RUN/snapshots.git, a repository the agent never sees. This is the
# fine-grained history its own commits do not give (it may commit rarely, or squash a subagent's work):
# a spec or proof rewritten between two of its commits shows up here.
# The files are copied first into runs/RUN/snapshots.tree (without .git dirs, so nested repositories,
# the agent's project and its fork, are recorded file by file): the work tree at its root, and every
# other checkout under /home/agent (a git worktree of the project, `git worktree add ../wt/X`, or a
# clone: where the agent's subagents work) under .lab-worktrees/NAME, NAME its path below /home/agent
# with % and / percent-encoded (wt/p-n1: .lab-worktrees/wt%2Fp-n1). A checkout inside the work tree
# (.claude/worktrees/X) is recorded with it. A pass commits only when something changed; each pass is a
# line of runs/RUN/snapshot.log (time, checkouts, the commit or "unchanged", seconds taken). The staging
# tree is removed when the container stops (snapshots.git has it all).
# Not recorded: .lake/, bin/, build output and plain clones of upstream repos (HEAD on a remote branch).
# DSV_SCOPE: the container's cgroup, while which it runs (default: the run's machine scope; for tests).
LAB=${DSV_LAB:?set DSV_LAB}
run=${1:?usage: snapshot.sh RUN}; R="$LAB/runs/$run"; H="$R/home"; W="$H/work"
S=${DSV_SCOPE:-/sys/fs/cgroup/machine.slice/dsverify-$run.scope}
T="$R/snapshots.tree"; WT=.lab-worktrees
# one snapshotter a run: a resume starts another while the last one may still be in its sleep
exec 9>>"$R/snapshot.lock"; flock -w 120 9 || exit 0
mkdir -p "$T"
export GIT_DIR="$R/snapshots.git" GIT_WORK_TREE="$T"
[ -d "$GIT_DIR/objects" ] || git init -q
git config user.name snapshot; git config user.email snapshot@lab; git config gc.auto 0
ag() { env -u GIT_DIR -u GIT_WORK_TREE git -c safe.directory='*' --no-optional-locks "$@"; }
# upstream DIR: rsync excludes for the plain clones of upstream repos inside checkout DIR
upstream() {
    find "$1" -maxdepth 3 -name .git -type d -not -path '*/.lake/*' | while read -r g; do
        d=$(dirname "$g"); [ "$d" = "$1" ] && continue
        [ -n "$(ag --git-dir="$g" --work-tree="$d" branch -r --contains HEAD 2>/dev/null)" ] && echo "--exclude=/${d#"$1"/}/"
    done
}
# checkouts: the agent's checkouts outside the work tree, as paths below its home: the work tree's
# worktrees (wherever they are), and any directory with a .git (a worktree of another repository, a
# clone) up to three levels down, but plain clones of upstream repos
checkouts() {
    {
        ag -C "$W" worktree list --porcelain 2>/dev/null | sed -n 's|^worktree /home/agent/||p'
        find "$H" -maxdepth 3 \( -path "$H/.*" -o -path "$H/go" -o -path "$H/tmp" -o -name .lake \) -prune -o -name .git -print 2>/dev/null |
            while read -r g; do
                d=$(dirname "$g")
                [ -d "$g" ] && [ -n "$(ag --git-dir="$g" --work-tree="$d" branch -r --contains HEAD 2>/dev/null)" ] && continue
                echo "${d#"$H"/}"
            done
    } | sort -u | while read -r p; do
        case "$H/$p/" in "$W/"*) continue ;; esac   # the work tree, or inside it: recorded with it
        [ -n "$p" ] && [ -d "$H/$p" ] && echo "$p"
    done
}
FILTER=(--exclude=.git --exclude=.lake/ --exclude=bin/ --include='*/' --include='*.lean' --include='*.go'
        --include='*.md' --include='*.toml' --include='*.py' --include='*.sh' --include='go.mod' --include='go.sum'
        --exclude='*')
while [ -d "$S" ]; do
    t=$SECONDS; stamp=$(date -u +%FT%TZ)
    # the work tree (keeping the checkouts' copies, which it does not hold)
    # shellcheck disable=SC2046
    rsync -a --delete --prune-empty-dirs --exclude="/$WT/" $(upstream "$W") "${FILTER[@]}" "$W/" "$T/" 2>>"$R/snapshot.err"
    mkdir -p "$T/$WT"; keep=()
    while read -r p; do
        n=${p//%/%25}; n=${n//\//%2F}; keep+=("$n")
        # shellcheck disable=SC2046
        rsync -a --delete --prune-empty-dirs $(upstream "$H/$p") "${FILTER[@]}" "$H/$p/" "$T/$WT/$n/" 2>>"$R/snapshot.err"
    done < <(checkouts)
    # checkouts removed since the last pass
    for d in "$T/$WT"/*/; do
        [ -d "$d" ] || continue; n=$(basename "$d")
        printf '%s\n' "${keep[@]}" | grep -qxF -- "$n" || rm -rf "$d"
    done
    git add -A 2>>"$R/snapshot.err"
    if git diff --cached --quiet 2>/dev/null; then c=unchanged
    else git commit -q -m "$stamp" 2>>"$R/snapshot.err"; c=$(git rev-parse --short HEAD); fi
    echo "$stamp checkouts $((${#keep[@]} + 1)) $c $((SECONDS - t))s" >>"$R/snapshot.log"
    sleep $(( (left = 60 - (SECONDS - t)) > 5 ? left : 5 ))
done
rm -rf "$T"
