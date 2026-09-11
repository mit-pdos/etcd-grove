#!/usr/bin/env bash
# Idempotently launches daemon.sh in the background if it isn't already running.
# Invoked from .claude/settings.json hooks (SessionStart, UserPromptSubmit). Must
# never block or print anything that could affect the conversation.
#
# Self-locates via $0 so this works regardless of which absolute path this repo
# is cloned to on a given machine (see daemon.sh for the same pattern).

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)"
DAEMON="$SCRIPT_DIR/daemon.sh"
STATE_DIR="$HOME/.claude/etcd-grove-sweep/state"
PIDFILE="$STATE_DIR/daemon.pid"
LOCKFILE="$STATE_DIR/daemon.lock"

mkdir -p "$STATE_DIR"

exec 9>"$LOCKFILE"
flock -n 9 || exit 0

if [ -f "$PIDFILE" ]; then
  pid=$(cat "$PIDFILE" 2>/dev/null)
  if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
    exit 0
  fi
fi

nohup setsid "$DAEMON" >>"$STATE_DIR/sweep.log" 2>&1 < /dev/null &
echo $! > "$PIDFILE"
disown

exit 0
