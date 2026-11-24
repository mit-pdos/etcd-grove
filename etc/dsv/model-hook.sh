#!/bin/bash
# PreToolUse hook on Agent/Task (managed-settings.json): every subagent runs on one model, Opus unless
# the run's config names another (`subagents`). The hook sets the call's `model`, whatever the agent
# asked for: the model parameter takes precedence over a built-in agent type's own model (Explore, ...);
# a fork ignores it and inherits the main session's model. The model is LAB_AGENT_MODEL (sandbox.sh
# start: the config's `subagents`, or opus); anything but opus, sonnet, haiku or fable counts as opus.
exec python3 -c '
import json, os, sys
d = json.load(sys.stdin)
ti = dict(d.get("tool_input") or {})
asked = ti.get("model")
want = os.environ.get("LAB_AGENT_MODEL", "opus")
if want not in ("opus", "sonnet", "haiku", "fable"): want = "opus"
ti["model"] = want
out = {"hookSpecificOutput": {"hookEventName": "PreToolUse", "permissionDecision": "allow",
       "permissionDecisionReason": "lab policy: every agent runs on %s" % want, "updatedInput": ti}}
if asked not in (None, want):
    out["systemMessage"] = "lab policy: subagent model %r replaced by %s" % (asked, want)
print(json.dumps(out))
'
