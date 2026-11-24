#!/bin/bash
# snapshot.sh RUN (as root, DSV_LAB set; experiment.sh starts it with nohup): while RUN's container
# runs, once a minute record the agent's work tree (Lean and Go sources, notes, configs) as a commit
# of runs/RUN/snapshots.git, a repository the agent never sees. This is the fine-grained history its
# own commits do not give (it may commit rarely, or squash a subagent's work): a spec or proof
# rewritten between two of its commits shows up here.
# The files are copied first into runs/RUN/snapshots.tree (without .git dirs, so nested repositories,
# the agent's project and its fork, are recorded file by file). Not recorded: .lake/, bin/, build
# output and plain clones of upstream repos (HEAD on a remote branch).
LAB=${DSV_LAB:?set DSV_LAB}
run=${1:?usage: snapshot.sh RUN}; R="$LAB/runs/$run"; W="$R/home/work"
S=/sys/fs/cgroup/machine.slice/dsverify-$run.scope
T="$R/snapshots.tree"; mkdir -p "$T"
export GIT_DIR="$R/snapshots.git" GIT_WORK_TREE="$T"
[ -d "$GIT_DIR/objects" ] || git init -q
git config user.name snapshot; git config user.email snapshot@lab; git config gc.auto 0
upstream() {
    find "$W" -maxdepth 3 -name .git -type d -not -path '*/.lake/*' | while read -r g; do
        d=$(dirname "$g")
        [ -n "$(git --git-dir="$g" --work-tree="$d" branch -r --contains HEAD 2>/dev/null)" ] && echo "--exclude=/${d#$W/}/"
    done
}
while [ -d "$S" ]; do
    # shellcheck disable=SC2046
    rsync -a --delete --prune-empty-dirs $(upstream) --exclude=.git --exclude=.lake/ --exclude=bin/ \
        --include='*/' --include='*.lean' --include='*.go' --include='*.md' --include='*.toml' \
        --include='*.py' --include='*.sh' --include='go.mod' --include='go.sum' --exclude='*' \
        "$W/" "$T/" 2>>"$R/snapshot.err"
    git add -A 2>>"$R/snapshot.err"
    git diff --cached --quiet 2>/dev/null || git commit -q -m "$(date -u +%FT%TZ)"
    sleep 60
done
