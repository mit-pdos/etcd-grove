#!/usr/bin/env bash
# Start a dsverify run, as root (in tmux): the token (asked for once), the container checks, then the
# agent with the run's opening prompt. Needs DSV_LAB and IMAGE (sandbox.sh).
#
#   run.sh RUN [PROMPT]   PROMPT: a file holding the opening prompt, or NAME for $DSV_LAB/prompts/NAME.txt;
#                         without it, the challenge's prompt.txt (kitgen --export-challenge writes it
#                         into DIR.lab; sandbox.sh new --challenge copies it to runs/RUN/goal/lab/)
#   run.sh RUN --continue resume RUN's last session (no check, no prompt)
set -euo pipefail
t0=$SECONDS
stage() { echo; echo "== [$1/3] $2  ($((SECONDS - t0))s elapsed)"; }
HERE=$(cd "$(dirname "$0")" && pwd)
run=${1:?usage: run.sh RUN [PROMPT|--continue]}; what=${2:-}
[ "$(id -u)" = 0 ] || exec sudo --preserve-env=DSV_LAB,DSV_TOKEN,IMAGE,LEAN_TOOLCHAIN "$0" "$@"
LAB=$(cd "${DSV_LAB:?set DSV_LAB to the experiment directory}" && pwd)
TOKEN=${DSV_TOKEN:-$LAB/token}
[ -d "$LAB/runs/$run" ] || { echo "no run $run (create it with sandbox.sh new $run --challenge DIR)"; exit 1; }

# 1. the token, once: a `claude setup-token` token in the token file (mode 600)
stage 1 "token"
tokenok() { grep -qE '^sk-ant-[A-Za-z0-9_-]{20,}$' "$TOKEN"; }
if [ -s "$TOKEN" ] && ! tokenok; then
    echo "$TOKEN does not look like a token (sk-ant-...): asking again"; rm -f "$TOKEN"
fi
if [ ! -s "$TOKEN" ]; then
    echo "No token yet. Run 'claude setup-token' first, under the account the experiment uses"
    echo "(it has you sign in in a browser and paste a code back into it), then paste the token it"
    echo "prints (sk-ant-oat01-...) here, then an empty line (input hidden; wrapping is fine):"
    token=""; while read -rs line && [ -n "$line" ]; do token+=$(printf '%s' "$line" | tr -d '[:space:]'); done; echo
    [ -n "$token" ] || { echo "empty token"; exit 1; }
    install -m 600 /dev/null "$TOKEN"; printf '%s\n' "$token" >"$TOKEN"
    tokenok || { rm -f "$TOKEN"; echo "that is not a token: it should start with sk-ant- (the browser's"
        echo "sign-in code goes into 'claude setup-token', which then prints the token)"; exit 1; }
    echo "saved $TOKEN"
else
    echo "using $TOKEN"
fi

if [ "$what" = --continue ]; then
    exec "$HERE/sandbox.sh" start "$run" --continue
fi
if [ -z "$what" ]; then prompt="$LAB/runs/$run/goal/lab/prompt.txt"
elif [ -f "$what" ]; then prompt=$what; else prompt="$LAB/prompts/$what.txt"; fi
[ -r "$prompt" ] || { echo "no prompt $prompt"; exit 1; }
echo "opening prompt: $prompt" 

# 2. the container check, proxy and all (in a throwaway run, so the real one stays untouched)
stage 2 "container check: isolation, proxy, offline Go and Lean builds (a few minutes)"
# (with this run's copy of the scripts)
SCRIPTS_OF="$LAB/runs/$run" "$HERE/sandbox.sh" start-shell test1 bash /opt/lab/check-env.sh 2>&1 | grep --line-buffered -v '^go: downloading' | tee "$LAB/runs/$run/check.log"
grep -q '^FAIL' "$LAB/runs/$run/check.log" && { echo "container check failed: not starting $run"; exit 1; }
grep -q 'proxy reaches api.anthropic.com' "$LAB/runs/$run/check.log" || { echo "proxy not checked: not starting $run"; exit 1; }
grep -q 'proxy reaches platform.claude.com' "$LAB/runs/$run/check.log" || { echo "proxy not checked: not starting $run"; exit 1; }
# a challenge run (sandbox.sh new --challenge): also its own view, the leak checks of the exported
# tree and its offline needs (check-env.sh --challenge; it changes nothing in the work tree)
if [ -f "$LAB/runs/$run/goal/challenge" ]; then
    echo "challenge run: the check in $run's own view (leaks, OFFLINE.txt, the challenge's checks; several minutes)"
    "$HERE/sandbox.sh" start-shell "$run" bash /opt/lab/check-env.sh --challenge 2>&1 | grep --line-buffered -v '^go: downloading' | tee "$LAB/runs/$run/check-challenge.log"
    grep -q '^FAIL' "$LAB/runs/$run/check-challenge.log" && { echo "challenge check failed: not starting $run"; exit 1; }
    grep -q '^PASS the skill is\|^PASS no skill' "$LAB/runs/$run/check-challenge.log" || { echo "challenge check incomplete: not starting $run"; exit 1; }
fi
echo "container check passed"

# 3. the agent
stage 3 "starting the agent in dsverify-$run (Claude Code takes over this terminal)"
# for experiment.sh launch: the container that runs from now on is the agent's (a challenge run's
# check ran in a container of the same name)
date -Is >"$LAB/runs/$run/stage3"
exec "$HERE/sandbox.sh" start "$run" "$(cat "$prompt")"
