#!/usr/bin/env python3
"""Stop hook: nudge an agent that changed proofs but left no notes.

Fires at most once per session, and only when the working tree has
uncommitted changes to hand-written `.v` files while `notes/` is untouched.
That combination means proof work happened and nothing durable was recorded.

Any other situation -- no proof changes, notes already updated, already
nudged once -- exits silently. On error it exits 0 rather than trapping the
agent.
"""

import datetime
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

# Generated trees: changes there are Goose output, not proof work.
GENERATED = ("new/code/", "new/generatedproof/")

REASON = """\
You changed proof files but did not touch `notes/`. This repo keeps persistent \
notes so the next agent -- possibly a fresh one with no history -- can pick the \
work up; see `notes/README.md`.

Before stopping, please either:
  1. update `notes/STATUS.md` (what moved, what is next) and append to \
`notes/journal/{date}.md`, plus `notes/gotchas.md`, `notes/topics/` or a \
`notes/decisions/` record if this session earned one -- the `/notes` skill \
walks through it; or
  2. if this session's work genuinely does not warrant a note (exploration \
that changed nothing, a whitespace fix), say so in one line and stop again.

Changed proof files:
{files}

This reminder fires only once per session."""


def git(*args: str) -> str:
    out = subprocess.run(["git", *args], capture_output=True, text=True, check=True)
    return out.stdout


def changed_paths() -> list[str]:
    """Paths differing from HEAD, tracked or not."""
    paths = set(git("diff", "HEAD", "--name-only").split())
    paths |= set(git("ls-files", "--others", "--exclude-standard").split())
    return sorted(paths)


def marker_for(session_id: str) -> Path:
    digest = hashlib.sha256(session_id.encode()).hexdigest()[:16]
    return Path(tempfile.gettempdir()) / f"etcd-grove-notes-nudge-{digest}"


def main() -> int:
    payload = json.loads(sys.stdin.read() or "{}")
    session_id = str(payload.get("session_id", ""))
    if not session_id:
        return 0

    marker = marker_for(session_id)
    if marker.exists():
        return 0

    paths = changed_paths()
    if any(p.startswith("notes/") for p in paths):
        return 0

    proof_files = [p for p in paths if p.endswith(".v") and not p.startswith(GENERATED)]
    if not proof_files:
        return 0

    marker.touch()
    # Local date, so the journal filename matches the agent's notion of today.
    today = datetime.datetime.now().astimezone().date().isoformat()
    shown = "\n".join(f"  {p}" for p in proof_files[:20])
    if len(proof_files) > 20:
        shown += f"\n  ... and {len(proof_files) - 20} more"

    print(
        json.dumps(
            {
                "decision": "block",
                "reason": REASON.format(date=today, files=shown),
            }
        )
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception:  # noqa: BLE001 - never trap the agent on a hook bug
        sys.exit(0)
