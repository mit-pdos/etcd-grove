#!/bin/bash
# Run inside the container: the bridge from 127.0.0.1:3128 to the host's proxy, then the agent.
python3 /opt/lab/proxy.py bridge /run/lab/proxy.sock 3128 &
for _ in $(seq 50); do (exec 3<>/dev/tcp/127.0.0.1/3128) 2>/dev/null && break; sleep 0.1; done
if [ "$1" = claude ]; then
    shift
    # the token (sandbox.sh binds it here rather than putting it on a command line)
    [ -r /run/lab-token ] && export CLAUDE_CODE_OAUTH_TOKEN="$(cat /run/lab-token)"
    umount /run/lab-token 2>/dev/null || true
    # "$@" (the prompt, or --continue) first: --disallowedTools takes a list and would swallow it
    # AskUserQuestion stays: nobody answers, but /opt/lab/ask-hook.sh (managed settings) replies to
    # every question with "take your recommendation", so the points where the skill asks still happen
    exec claude "$@" --strict-mcp-config --disallowedTools "WebFetch,WebSearch,RemoteTrigger"
fi
exec "$@"
