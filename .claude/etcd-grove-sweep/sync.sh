#!/usr/bin/env bash
# Mirrors every Claude Code chat transcript for this project into
# git@github.com:upamanyus/etcd-grove-prompts.git.
#
# Invoked from .claude/settings.json (SessionStart, Stop, SessionEnd). Does one
# pull/copy/commit/push pass and exits; there is no daemon and nothing is left
# running afterwards.
#
# Two things about where transcripts live drive the design:
#
#  - A project's transcripts are ~/.claude/projects/<slug of the session cwd>,
#    and a git worktree has its own cwd, hence its own project dir. Every
#    worktree of this repo therefore has to be swept, not just the checkout
#    whose hook fired.
#  - Subagent chats are *.jsonl nested under <session-id>/subagents/, so the
#    sweep recurses rather than globbing the top level of each project dir.

set -u

STATE_DIR="$HOME/.claude/etcd-grove-sweep"
MIRROR_DIR="$STATE_DIR/mirror"
LOG="$STATE_DIR/sync.log"
REMOTE="git@github.com:upamanyus/etcd-grove-prompts.git"

mkdir -p "$STATE_DIR"

# Re-exec detached when run from a hook. Hooks must not block the session, and
# SessionEnd hooks share a 1.5s budget a push that ran inline would exceed.
# Run by hand from a terminal it stays in the foreground and reports to stdout,
# so you can see the push land when you want a transcript saved right now.
if [ -z "${SWEEP_DETACHED:-}" ] && [ ! -t 1 ]; then
  SWEEP_DETACHED=1 setsid nohup "$0" >>"$LOG" 2>&1 </dev/null &
  exit 0
fi

log() { echo "[$(date -Iseconds)] $*"; }

# One pass at a time; concurrent passes would race in the same clone.
exec 9>"$STATE_DIR/sync.lock"
flock -w 120 9 || { log "another pass holds the lock, skipping"; exit 0; }

[ "$(stat -c %s "$LOG" 2>/dev/null || echo 0)" -gt 1000000 ] && : >"$LOG"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

if [ ! -d "$MIRROR_DIR/.git" ]; then
  log "cloning $REMOTE"
  rm -rf "$MIRROR_DIR"
  git clone -q "$REMOTE" "$MIRROR_DIR" || { log "clone failed"; exit 1; }
fi

# Transcript dirs for this checkout and every other worktree of the same repo.
# Claude Code slugs the cwd by replacing every character outside [A-Za-z0-9_-]
# with '-', so /a/b/.claude/c becomes -a-b--claude-c: the dot collapses too, not
# just the slashes. Getting that wrong silently skips a whole worktree, so warn
# when a computed dir is absent instead of quietly sweeping nothing.
sources=()
while IFS= read -r worktree; do
  [ -n "$worktree" ] || continue
  src="$HOME/.claude/projects/$(printf '%s' "$worktree" | tr -c 'A-Za-z0-9_-' '-')"
  if [ -d "$src" ]; then
    sources+=("$src")
  else
    log "no transcripts for $worktree (no session ran there, or the slug rule changed)"
  fi
done < <(git -C "$REPO_DIR" worktree list --porcelain | sed -n 's/^worktree //p')

if [ "${#sources[@]}" -eq 0 ]; then
  log "no transcript dirs found for $REPO_DIR, nothing to sync"
  exit 0
fi

cd "$MIRROR_DIR" || exit 1
branch="$(git symbolic-ref --short HEAD)"

# A hook can run without git's global identity visible (unusual HOME, launchd,
# a machine where it was never set). Without an identity `git commit` fails, and
# the push that follows then succeeds as a no-op - transcripts would be dropped
# while everything looked fine. Fall back to a local one rather than risk that.
git config user.name >/dev/null || git config user.name "etcd-grove-sweep"
git config user.email >/dev/null || git config user.email "etcd-grove-sweep@localhost"

# The mirror is derived state: ~/.claude/projects is the only source of truth, so
# each attempt rebuilds from origin and re-copies instead of trying to reconcile
# a local commit with a concurrent one from another machine. Retries cover origin
# moving underneath us mid-pass.
for attempt in 1 2 3; do
  git fetch -q origin
  if git rev-parse --verify -q "origin/$branch" >/dev/null; then
    git reset -q --hard "origin/$branch"
  fi

  mkdir -p "$MIRROR_DIR/sessions"
  for src in "${sources[@]}"; do
    # Live sessions are appended to as this runs, so the final line of a
    # transcript can land truncated; the next pass copies it whole.
    ( cd "$src" && find . -name '*.jsonl' -print0 |
        xargs -0 -r cp -a --parents -t "$MIRROR_DIR/sessions/" )
  done

  git add -A
  if git diff --cached --quiet; then
    log "up to date"
    exit 0
  fi
  if ! git commit -q -m "sync: $(date -Iseconds)"; then
    log "commit failed, nothing pushed (see error above)"
    exit 1
  fi

  if git push -q origin "HEAD:$branch" 2>>"$LOG"; then
    log "pushed $(git rev-parse --short HEAD) covering ${#sources[@]} worktree(s)"
    exit 0
  fi
  log "push failed (attempt $attempt)"
done

log "giving up after 3 attempts; next hook will retry"
exit 1
