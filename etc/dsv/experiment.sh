#!/bin/bash
# Running experiments unattended (as root; needs DSV_LAB and IMAGE, as sandbox.sh does).
#
#   experiment.sh launch RUN [PROMPT] run.sh RUN [PROMPT] in a detached tmux session named RUN (PROMPT:
#                                     run.sh's; default the challenge's prompt.txt); returns once
#                                     the agent has started (or the check failed); starts loadlog.sh
#                                     and snapshot.sh
#   experiment.sh wait RUN [HOURS]    returns when RUN's agent is done: Claude Code is not working (no
#                                     "esc to interrupt" on its screen), no session or subagent has made a
#                                     tool call for IDLE minutes (default 20; wakeups that only talk or
#                                     schedule do not count), and no Lean/Go/test process runs; or after HOURS
#                                     (default 12). Prints DONE, TIMEOUT, EXITED or DIALOG.
#                                     While Claude Code shows "Usage limit reached" (it resumes by
#                                     itself when the limit resets) the run is not done; the limit's
#                                     dialog ("What do you want to do?") is answered 2, wait and
#                                     continue, and logged in runs/RUN/interventions.log. "You've hit
#                                     your weekly limit" (API errors; the session then sits idle at its
#                                     prompt and does not resume by itself) is a usage limit too: not
#                                     done, and swapped to a staged TOKEN.next if there is one, also
#                                     one staged later. Any other
#                                     dialog (a permission prompt) is not done either: after a minute
#                                     on the screen it ends the wait with DIALOG (exit 3) and the
#                                     screen's last lines, for someone to answer.
#   experiment.sh resume RUN MESSAGE  RUN's last session again (run.sh RUN --continue) in a new tmux
#                                     session, then MESSAGE typed into it; loadlog.sh and snapshot.sh
#                                     restarted; logged in runs/RUN/interventions.log
#   (wait, at the usage limit with a staged TOKEN.next: swaps the token and resumes the run; see retoken)
#   experiment.sh finish RUN          closes the session (the container stops), tags the project's newest
#                                     branch `final` (unless already tagged), and runs sandbox.sh verify RUN final
# A run's screen: sudo tmux attach -t RUN (detach: ctrl-b d).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
cmd=${1:?usage: experiment.sh launch|wait|resume|finish RUN ...}; run=${2:?RUN}
[ "$(id -u)" = 0 ] || exec sudo --preserve-env=DSV_LAB,DSV_TOKEN,IMAGE,LEAN_TOOLCHAIN,VERIFY_RUN,IDLE "$0" "$@"
LAB=$(cd "${DSV_LAB:?set DSV_LAB to the experiment directory}" && pwd)
# the token file (sandbox.sh): TOKEN.next, staged beside it, is swapped in at a usage limit
TOKEN=${DSV_TOKEN:-$LAB/token}
# the environment the scripts started in tmux need (a tmux server started earlier has its own)
export DSV_LAB=$LAB DSV_TOKEN=$TOKEN   # for loadlog.sh and snapshot.sh
TENV="DSV_LAB=$(printf %q "$LAB") DSV_TOKEN=$(printf %q "$TOKEN") IMAGE=$(printf %q "${IMAGE:-}")${LEAN_TOOLCHAIN:+ LEAN_TOOLCHAIN=$(printf %q "$LEAN_TOOLCHAIN")}"
R="$LAB/runs/$run"; [ -d "$R" ] || { echo "no run $run"; exit 1; }
S=/sys/fs/cgroup/machine.slice/dsverify-$run.scope
screen() { tmux capture-pane -p -t "$run" -S -60 2>/dev/null; }
# worked_within PROJECTS MIN: some session or subagent made a tool call in the last MIN minutes. Turns that only
# talk or schedule (a /loop or cron wakeup finding nothing to do: text, ScheduleWakeup, Cron*) are not work, so
# they do not keep a finished run from counting as done.
worked_within() {
    find "$1" -name '*.jsonl' -mmin -"$2" -print0 2>/dev/null | python3 -c '
import sys, json, datetime
cut = datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(minutes=int(sys.argv[1]))
noop = {"ScheduleWakeup", "CronCreate", "CronDelete", "CronList"}
for f in sys.stdin.read().split("\0"):
    if not f: continue
    for line in open(f, errors="replace"):
        try: d = json.loads(line)
        except ValueError: continue
        m = d.get("message")
        if d.get("type") != "assistant" or not isinstance(m, dict): continue
        if not any(isinstance(c, dict) and c.get("type") == "tool_use" and c.get("name") not in noop
                   for c in m.get("content") or []): continue
        try: t = datetime.datetime.fromisoformat(d["timestamp"].replace("Z", "+00:00"))
        except (KeyError, ValueError): continue
        if t >= cut: sys.exit(0)
sys.exit(1)' "$2"
}
# dialog: Claude Code shows a dialog and waits for a key (the last lines of its screen; an
# AskUserQuestion never gets this far: ask-hook.sh answers it). limit_dialog: the usage limit's.
dialog() { screen | grep -v '^\s*$' | tail -12 | grep -qE 'Enter to confirm · Esc to cancel|Esc to cancel · Tab to amend'; }
# limit_text: the usage limit's messages ("Usage limit reached"; "You've hit your weekly limit" in
# API errors, the main session's and its subagents', after which the session idles at its prompt)
limit_text() { screen | grep -qE "Usage limit reached|You've hit your [a-z]+ limit"; }
limit_dialog() {
    local s; s=$(screen | grep -v '^\s*$' | tail -12)
    echo "$s" | grep -q 'Stop and wait for limit to reset' && echo "$s" | grep -q 'Wait here, then continue automatically' &&
        echo "$s" | grep -q 'Enter to confirm'
}
# busy_procs: Lean, Lake, Go and test processes in the run's container (a long build or test writes nothing
# to the transcripts while it runs)
busy_procs() {
    local pids; pids=$(cat $(find "$S" -name cgroup.procs 2>/dev/null) 2>/dev/null | tr '\n' ',' | sed 's/,$//')
    [ -n "$pids" ] || { echo 0; return; }
    ps -o comm= -p "$pids" 2>/dev/null | grep -cE '^(lean|lake|go|compile|link|asm|.*\.test)$'
}
log() { echo "$(date -u +%H:%M) $run: $*"; }
# retoken: at the usage limit, with a staged TOKEN.next (another `claude setup-token` token, root 600,
# beside the token file TOKEN): the spent token is kept as TOKEN.spent-TIME, TOKEN.next becomes TOKEN,
# the session is closed (its container stops: the token is read only at a container's start) and
# resumed with --continue. Every run started with the same TOKEN shares it: a second run at the limit
# after the swap finds no TOKEN.next but a token newer than its container (token_newer) and is resumed
# the same way.
retoken() {
    local ts; ts=$(date -u +%Y%m%dT%H%M%SZ)
    if [ -f "$TOKEN.next" ]; then
        mv "$TOKEN" "$TOKEN.spent-$ts" && mv "$TOKEN.next" "$TOKEN" && chmod 600 "$TOKEN" && touch "$TOKEN" || return 1
        echo "$ts" >"$TOKEN.swapped-at"
    fi
    tmux kill-session -t "$run" 2>/dev/null
    for _ in $(seq 60); do [ -d "$S" ] || break; sleep 1; done
    [ -d "$S" ] && { log "retoken: container still running"; return 1; }
    local X=/run/systemd/nspawn/unix-export/dsverify-$run
    if [ -e "$X" ]; then mountpoint -q "$X" && umount "$X"; rmdir "$X"; fi
    echo "$(date -u +%FT%TZ) wait: usage limit reached; the lab swapped the account's token (staged TOKEN.next, swapped at $(cat "$TOKEN.swapped-at")) and resumed the session (--continue); nothing else changed" >>"$R/interventions.log"
    "$0" resume "$run" "The session was restarted after a usage limit (the lab switched accounts). Your work tree and history are as you left them; background jobs and subagents that were running have stopped. Check what was in flight and continue where you left off."
}
# a token newer than this run's container: the run is still on the spent one
token_newer() { [ -f "$TOKEN.swapped-at" ] && [ "$TOKEN" -nt "$S" ]; }

case $cmd in
launch)
    prompt=${3:-}
    tmux has-session -t "$run" 2>/dev/null && { log "a session $run exists already"; exit 1; }
    [ -d "$S" ] && { log "its container is running already"; exit 1; }
    rm -f "$R/stage3"
    tmux new-session -d -s "$run" -x 220 -y 50 "$TENV $(printf %q "$HERE/run.sh") $run ${prompt:+$(printf %q "$prompt")}; echo; echo \"run.sh exited \$?\"; exec bash"
    log "launched (prompt ${prompt:-runs/$run/goal/lab/prompt.txt})"
    # (a challenge run's checks, in its own view too, take longer: up to an hour)
    for _ in $(seq 720); do
        out=$(screen)
        if echo "$out" | grep -qE 'not starting|run.sh exited'; then log "did not start:"; echo "$out" | grep -v '^\s*$' | tail -15; exit 1; fi
        # the agent's container: stage 3 reached (run.sh writes runs/RUN/stage3; a challenge run's
        # check, in stage 2, runs in a container of the same name) and the container up
        if [ -f "$R/stage3" ] && [ -d "$S" ]; then
            nohup "$HERE/loadlog.sh" "$run" >/dev/null 2>&1 </dev/null &
            nohup "$HERE/snapshot.sh" "$run" >/dev/null 2>&1 </dev/null &
            log "agent started; logging load, snapshotting the work tree"; exit 0
        fi
        sleep 5
    done
    log "not started after 60 minutes"; exit 1 ;;
resume)
    msg=${3:?usage: experiment.sh resume RUN MESSAGE}
    tmux has-session -t "$run" 2>/dev/null && { log "a session $run exists already"; exit 1; }
    [ -d "$S" ] && { log "its container is running already"; exit 1; }
    tmux new-session -d -s "$run" -x 220 -y 50 "$TENV $(printf %q "$HERE/run.sh") $run --continue; echo; echo \"run.sh exited \$?\"; exec bash"
    for _ in $(seq 120); do [ -d "$S" ] && screen | grep -q '❯' && break; sleep 5; done
    [ -d "$S" ] || { log "did not start:"; screen | grep -v '^\s*$' | tail -15; exit 1; }
    sleep 10   # the session's history is still loading
    tmux send-keys -t "$run" -l "$msg"; sleep 1; tmux send-keys -t "$run" Enter
    echo "$(date -u +%FT%TZ) resume: $msg" >>"$R/interventions.log"
    nohup "$HERE/loadlog.sh" "$run" >/dev/null 2>&1 </dev/null &
    nohup "$HERE/snapshot.sh" "$run" >/dev/null 2>&1 </dev/null &
    log "resumed; message sent; logging load, snapshotting the work tree"; exit 0 ;;
wait)
    hours=${3:-12}; idle=${IDLE:-20}; t0=$SECONDS
    P="$R/home/.claude/projects"
    while :; do
        [ -d "$S" ] || { log "EXITED (container gone)"; exit 0; }
        # the usage limit's dialog: answered here (option 2), since nothing resumes the run otherwise
        if limit_dialog || limit_text; then
            if [ -f "$TOKEN.next" ] || token_newer; then
                log "usage limit reached: switching to the next token and resuming"
                if retoken; then log "resumed on the new token"; limited=; sleep 120; continue; fi
                log "retoken failed; falling back to waiting for the reset"
            fi
        fi
        if limit_dialog; then
            tmux send-keys -t "$run" Down; sleep 2
            if screen | grep -qE '❯ *2\. Wait here, then continue automatically'; then
                tmux send-keys -t "$run" Enter
                log "usage limit dialog: answered 2 (wait here, then continue automatically)"
                echo "$(date -u +%FT%TZ) wait: usage limit dialog answered 2 (Wait here, then continue automatically); nothing else typed" >>"$R/interventions.log"
                limited=1; sleep 60; continue
            fi
            log "DIALOG (the usage limit's, not in the form expected; answer it by hand):"; screen | grep -v '^\s*$' | tail -12; exit 3
        fi
        # any other dialog (a permission prompt, a confirmation): Claude Code waits for a key and the
        # run is not done; seen on two checks a minute apart, it ends the wait
        if dialog; then
            if [ -n "${asked:-}" ]; then log "DIALOG (waiting for an answer; sudo tmux attach -t $run):"; screen | grep -v '^\s*$' | tail -15; exit 3; fi
            asked=1; sleep 60; continue
        fi
        asked=
        if limit_text; then
            [ -n "${limited:-}" ] || log "usage limit reached; waiting for the reset (or a staged TOKEN.next; after a weekly limit's API errors the session idles at its prompt and needs a resume)"; limited=1; sleep 60; continue
        fi
        [ -n "${limited:-}" ] && { log "working again after the usage limit"; limited=; }
        if ! screen | grep -q 'esc to interrupt' &&
           [ -n "$(find "$P" -name '*.jsonl' 2>/dev/null | head -1)" ] &&
           ! worked_within "$P" "$idle" && [ "$(busy_procs)" = 0 ]; then
            log "DONE (no work for $idle min)"; exit 0
        fi
        [ $((SECONDS - t0)) -gt $((hours * 3600)) ] && { log "TIMEOUT after $hours h"; exit 2; }
        sleep 60
    done ;;
finish)
    screen | grep -v '^\s*$' | tail -40 >"$R/final-screen.txt"
    tmux kill-session -t "$run" 2>/dev/null
    for _ in $(seq 30); do [ -d "$S" ] || break; sleep 1; done
    [ -d "$S" ] && { log "container still running"; exit 1; }
    X=/run/systemd/nspawn/unix-export/dsverify-$run
    if [ -e "$X" ]; then mountpoint -q "$X" && umount "$X"; rmdir "$X"; fi
    # the project: a challenge run's work tree itself (sandbox.sh new --challenge)
    P="$R/home/work"
    [ -f "$R/goal/challenge" ] && [ -d "$P/.git" ] || { log "not a challenge run, or no repository in $P"; exit 1; }
    g() { git -c safe.directory='*' -C "$P" "$@"; }
    if g rev-parse -q --verify refs/tags/final >/dev/null; then log "tag final exists: $(g rev-parse --short final)"
    else
        # the newest branch, not HEAD: an agent may work on a branch in a worktree and never merge it
        b=$(g for-each-ref --sort=-committerdate --format='%(refname:short)' refs/heads | head -1)
        g tag final "$b" && log "tagged final at $b: $(g log -1 --format='%h %s' "$b")"
    fi
    [ -z "$(g status --porcelain --untracked-files=no)" ] || log "note: uncommitted changes in $P (not verified)"
    "$HERE/sandbox.sh" verify "$run" final </dev/null >/dev/null 2>&1   # stdin not a terminal: nspawn kills the container otherwise (ssh without -t)
    log "verify: $(grep -E '^== (NOT )?verified' "$R/verify-final.log" | tail -1)" ;;
*) sed -n '2,30p' "$0"; exit 1 ;;
esac
