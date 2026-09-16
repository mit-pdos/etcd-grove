# notes/ — persistent project memory

Plain markdown, committed to the repo. It exists so that **a fresh agent or
person, with no conversation history, can pick up the work** by reading these
files. No tooling, no hooks, no required format — any coding agent can read and
write them.

If a fact only matters inside one conversation, it does not belong here.

## The files

- **[STATUS.md](STATUS.md)** — where the proof is right now, what is in flight,
  what is next, what is known broken. **Start here.**
- **[raft-implementation-facts.md](raft-implementation-facts.md)** — what
  etcd raft *actually does*, where the proof had assumed otherwise. Read
  before assuming anything about a raft function.
- **[gotchas.md](gotchas.md)** — traps that have already cost someone time.
- **[raft-proof-map.md](raft-proof-map.md)** — what is in each Raft proof file
  and how they fit together.
- **[raft-election-refinement.md](raft-election-refinement.md)** — the
  leader-election refinement proof: scope, what is proved, what is admitted,
  and where the trust boundary is.
- **[goose-workflow.md](goose-workflow.md)** — how Go source in the etcd forks
  becomes Rocq in `new/code/`, and how to change it.
- **[decisions.md](decisions.md)** — why the development is the way it is.
  Newest last.
- **[journal.md](journal.md)** — dated log of what happened. For archaeology
  ("why did this break?"), not orientation. Newest last, append-only.

## Before you finish a session

Update `STATUS.md` if anything moved, and append a dated entry to
`journal.md`. Add to `gotchas.md`, a topic file, or `decisions.md` when the
session earned it. That's the whole contract — nothing enforces it, so it is on
you.

## Conventions

- **Write for a stranger.** No "as discussed", no "the file we were looking
  at". Name files by path, lemmas by name, with line numbers where useful
  (`new/proof/go_etcd_io/raft/v3_proof/readonly.v:295`).
- **Absolute dates.** "2026-09-11", never "yesterday".
- **Record the dead ends.** A failed approach and *why* it failed is often
  worth more than the one that worked, because the next agent will otherwise
  try it again.
- **Correct, don't append** — except in `journal.md`, which is append-only.
  Stale text in `STATUS.md` is worse than no text, because it gets trusted.
  Superseded decisions get a "Superseded by …" line rather than deletion.
- **Keep `STATUS.md` short enough to be read** (~150 lines). Push detail into a
  topic file.

## Add structure only when it has earned it

This directory started out with `topics/`, `decisions/` and `journal/`
subdirectories, per-directory index and template files, two Python hook scripts
and a Claude-Code-specific skill. Almost all of that was scaffolding with no
content in it, and the hooks tied the notes to one particular agent. It was
replaced with seven flat markdown files on 2026-09-11.

So: when one of these files gets unwieldy, split it. When a step is genuinely
being forgotten every time, automate that step. Not before — speculative
structure costs maintenance, goes stale, and in the hooks' case locks the
project to one tool.

## What does *not* go here

- Anything derivable from the code, `git log`, or CI.
- Perennial tactic documentation — that lives in
  `new/proof/PERENNIAL_PROOF_TUTORIAL.md`,
  `new/proof/PERENNIAL_PROOF_REFERENCE.md`, and `docs/style_guide.md`. Note
  here only what those get wrong or omit.
- Secrets or credentials of any kind.
