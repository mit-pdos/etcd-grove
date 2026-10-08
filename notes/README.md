# notes/ — the project's shared memory

Plain markdown, committed on `lean`. It exists so that **an agent or person with no
conversation history can pick up the work**, and so that many of them can work at
once without talking to each other except through these files.

## The files

- **[STATUS.md](STATUS.md)**: where the proof is right now. No history. Start here.
- **[roadmap.md](roadmap.md)**: the directions toward verifying all of etcd, ranked,
  each with its design doc and tasks. Kept in line with `../manual-notes.txt`
  (people's standing directions, which agents never edit): its `manual-notes:` line
  records the version of that file it reflects. *(Written by the first
  `roadmap-sync` task.)*
- **[collaboration.md](collaboration.md)**: how people and agents coordinate:
  tasks, chat, claiming, landing, review.
- **[tasks/](tasks/README.md)**: one file per task (`etc/tasks.py`).
- **[chat/](chat/README.md)**: one thread per big idea, between people and agents.
- **design/**: one design doc per topic (`design/<topic>.md`): the property, the
  code, the trust boundary, the interfaces, the task breakdown.
- **[decisions.md](decisions.md)**: why the development is the way it is. Newest last.
- **[porting-guide.md](porting-guide.md)**: Rocq → Lean idioms.
- **[archive/](archive/README.md)**: finished one-off briefs; don't follow them.

The Rocq development's notes on `main` (`git show main:notes/<file>`) are a
read-only reference: `false-statements.md` (claims that turned out false, and the
tells), `raft-implementation-facts.md`, `gotchas.md`. When one is needed here, port
it to `notes/` rather than re-deriving it.

There is no journal: with many agents an append-only log is a permanent merge
conflict. A task's `## Log` records its work, and `git log` the rest.

## Conventions

- **Write for a stranger.** No "as discussed". Name files by path and lemmas by
  name, with line numbers where useful.
- **Absolute dates**: "2026-10-08", never "yesterday".
- **Record the dead ends.** A failed approach and why it failed is often worth
  more than the one that worked.
- **Correct, don't append**, except in chat threads and task logs. Stale text in
  `STATUS.md` is worse than none, because it gets trusted. A superseded decision
  gets a "Superseded by …" line rather than deletion.
- **Keep `STATUS.md` short** (~150 lines); push detail into a topic file.
- No secrets or credentials, ever.

## Add structure only when it has earned it

When a file gets unwieldy, split it. When a step is forgotten every time, automate
it (as `etc/tasks.py` and `etc/land.py` automate the coordination steps). Not before.
