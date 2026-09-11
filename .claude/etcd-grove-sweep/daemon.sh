#!/usr/bin/env bash
# Background sweep daemon: mirrors this project's Claude Code session transcripts
# into a git repo every SYNC_INTERVAL seconds, and exits on its own once the
# project has been idle for IDLE_TIMEOUT seconds (no new transcript writes).
# Only ever launched by ensure-daemon.sh - never run directly or via cron.
#
# Derives the transcript source directory from this script's own location
# (two levels up is the project root), so it works no matter which absolute
# path this repo is cloned to.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
SOURCE_DIR="$HOME/.claude/projects/$(printf '%s' "$PROJECT_DIR" | tr '/' '-')"
MIRROR_DIR="$HOME/.claude/etcd-grove-sweep/mirror"
STATE_DIR="$HOME/.claude/etcd-grove-sweep/state"
PIDFILE="$STATE_DIR/daemon.pid"
REMOTE="git@github.com:upamanyus/etcd-grove-prompts.git"
SYNC_INTERVAL=60
IDLE_TIMEOUT=600

log() { echo "[$(date -Iseconds)] $*"; }

mkdir -p "$STATE_DIR"
daemon_start=$(date +%s)
log "daemon started pid=$$ project=$PROJECT_DIR source=$SOURCE_DIR"

if [ ! -d "$MIRROR_DIR/.git" ]; then
  log "cloning mirror repo"
  rm -rf "$MIRROR_DIR"
  if ! git clone "$REMOTE" "$MIRROR_DIR" >>"$STATE_DIR/sweep.log" 2>&1; then
    log "clone failed, exiting"
    rm -f "$PIDFILE"
    exit 1
  fi
fi

while true; do
  latest_mtime=0
  shopt -s nullglob
  files=("$SOURCE_DIR"/*.jsonl)
  shopt -u nullglob
  if [ "${#files[@]}" -gt 0 ]; then
    latest_mtime=$(stat -c %Y "${files[@]}" 2>/dev/null | sort -n | tail -1)
    [ -z "$latest_mtime" ] && latest_mtime=0
  fi
  now=$(date +%s)
  idle=$(( now - latest_mtime ))
  alive=$(( now - daemon_start ))

  # Being launched at all is evidence of current activity, and the write that
  # triggered this launch may not have hit disk yet - so never self-terminate
  # before this daemon has been alive for a full IDLE_TIMEOUT itself, even if
  # pre-existing files already looked stale at startup.
  if { [ "$latest_mtime" -eq 0 ] || [ "$idle" -gt "$IDLE_TIMEOUT" ]; } && [ "$alive" -gt "$IDLE_TIMEOUT" ]; then
    log "idle ${idle}s (limit ${IDLE_TIMEOUT}s), stopping"
    rm -f "$PIDFILE"
    exit 0
  fi

  cd "$MIRROR_DIR" || exit 1
  git pull --rebase -q >>"$STATE_DIR/sweep.log" 2>&1

  mkdir -p "$MIRROR_DIR/sessions"
  cp -a "$SOURCE_DIR"/*.jsonl "$MIRROR_DIR/sessions/" 2>/dev/null

  git add -A
  if ! git diff --cached --quiet; then
    git commit -q -m "sync: $(date -Iseconds)"
    if git push -q >>"$STATE_DIR/sweep.log" 2>&1; then
      log "pushed changes"
    else
      log "push failed, will retry next tick"
    fi
  fi

  sleep "$SYNC_INTERVAL"
done
