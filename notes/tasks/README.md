# Tasks

One file per task, `<id>.md`. Change the frontmatter only with `etc/tasks.py`
(`etc/tasks.py --help`); the body is free text. See `notes/collaboration.md`, "Tasks".

```markdown
---
id: cindex-setconsistentindex       # = the file name; lower-case, digits, . _ -
title: Spec and prove cindex.consistentIndex.SetConsistentIndex
kind: proof            # proof | spec | translation | framework | design | infra | review | fix-lean
state: open            # open | claimed | review | reviewing | needs-human | done | dropped
priority: 1            # 1 = serves a manual-notes.txt direction; 2 = on its path; 3 = the rest
design: notes/design/consistent-index.md
depends: [goose-cindex]
owner:                 # git user.email of the claiming agent's person (claimed, reviewing)
claimed-at:
implementer:           # who implemented it (review, reviewing)
branch:                # task/<id>: the work in progress, and the handoff
---

# <title>

## Goal
What is true when this is done, in terms of files and theorems.

## Context
Pointers: design doc section, Go source (file:line at the pinned fork), callees' specs.

## Log
Dated entries by whoever works on it: what was done, where it stopped, dead ends.

## History
(written by etc/tasks.py: created, claimed, released, landed …)
```

A task is one landing: a few hours of agent work, typically one Go function's spec
and proof. A task whose `depends` are not all `done` can't be claimed.
