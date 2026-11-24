#!/bin/bash
# PreToolUse hook on AskUserQuestion (managed-settings.json): nobody answers during a run, so every
# question gets this reply. The agent still reaches the points where the skill has it ask (a freeze,
# a new trusted statement), and does what precedes them; only the answer is automatic.
cat >/dev/null
cat <<'JSON'
{"hookSpecificOutput": {"hookEventName": "PreToolUse", "permissionDecision": "deny",
 "permissionDecisionReason": "No user is available during this run; this automatic reply stands in for the answer. Take the option you would recommend, record it in notes/decisions.md as your own decision (\"decided by the agent; no user in this run\") with your reasons, and continue. Asking was not a mistake: do everything the workflow requires at this point before going on."}}
JSON
