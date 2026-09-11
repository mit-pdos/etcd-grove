#!/usr/bin/env python3
"""SessionStart hook: hand every fresh agent the repo's persistent notes.

Reads the hook payload on stdin (unused beyond knowing we were invoked) and
prints a JSON object whose `additionalContext` is an orientation blob built
from `notes/`. See notes/README.md for the contract this enforces.

Never fails the session: on any error it prints nothing and exits 0.
"""

import json
import subprocess
import sys
from pathlib import Path

# Files injected verbatim, in order. Anything larger lives in notes/topics/ and
# is listed rather than inlined, to keep the injected context small.
INLINE = ["STATUS.md", "gotchas.md"]

# Only list, don't inline, from these directories.
LISTED = ["topics", "decisions", "journal"]

MAX_CHARS = 24000


def repo_root() -> Path:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
            check=True,
        )
        return Path(out.stdout.strip())
    except (OSError, subprocess.CalledProcessError):
        return Path.cwd()


def listing(notes: Path, subdir: str) -> list[str]:
    d = notes / subdir
    if not d.is_dir():
        return []
    names = sorted(p.name for p in d.glob("*.md") if p.name != "README.md")
    if not names:
        return []
    if subdir == "journal":
        # Most recent first; the whole history is rarely relevant.
        names = list(reversed(names))[:8]
    return [f"- `notes/{subdir}/{n}`" for n in names]


def build_context(notes: Path) -> str:
    parts = [
        "# Persistent project notes (`notes/`)",
        "",
        "This repo keeps durable, committed notes so that a fresh agent has the",
        "context it needs. `notes/README.md` is the contract: read `STATUS.md`",
        "first, and **update `notes/` before you finish** — at minimum",
        "`notes/STATUS.md` and today's `notes/journal/YYYY-MM-DD.md`. The",
        "`/notes` skill walks through it.",
        "",
    ]

    for name in INLINE:
        f = notes / name
        if not f.is_file():
            continue
        parts += [f"## notes/{name}", "", f.read_text().rstrip(), ""]

    for subdir in LISTED:
        entries = listing(notes, subdir)
        if not entries:
            continue
        label = "most recent journal entries" if subdir == "journal" else subdir
        parts += [f"## Available {label}", ""] + entries + [""]

    text = "\n".join(parts)
    if len(text) > MAX_CHARS:
        text = text[:MAX_CHARS] + "\n\n[truncated — read notes/ directly]"
    return text


def main() -> int:
    # Drain stdin so the caller never sees a broken pipe.
    sys.stdin.read()

    notes = repo_root() / "notes"
    if not (notes / "STATUS.md").is_file():
        return 0

    print(
        json.dumps(
            {
                "suppressOutput": True,
                "hookSpecificOutput": {
                    "hookEventName": "SessionStart",
                    "additionalContext": build_context(notes),
                },
            }
        )
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception:  # noqa: BLE001 - a hook must never break the session
        sys.exit(0)
