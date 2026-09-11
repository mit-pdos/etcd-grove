# notes/ — persistent project memory

This directory is the durable, version-controlled memory for the etcd
verification effort. It exists so that a **fresh agent, with no conversation
history, can pick up the work** by reading files here.

Everything in here is committed. If a fact only matters inside one
conversation, it does not belong here.

## Read this first (in order)

1. **[STATUS.md](STATUS.md)** — where the proof is right now, what is in
   flight, what is next. Always current; this is the entry point.
2. **[gotchas.md](gotchas.md)** — traps that have already cost someone an hour.
   Read before touching a proof.
3. **[topics/](topics/)** — durable technical notes: the shape of a proof, how
   a piece of tooling works, a summary of the etcd code being verified.
4. **[decisions/](decisions/)** — why the development is the way it is. Read
   the relevant one before changing a spec or an invariant.
5. **[journal/](journal/)** — dated, append-only log of what happened. Consult
   for archaeology ("why did this break?"), not for orientation.

## Write this before you finish

Every agent session that does real work updates notes. Cheapest useful thing
first:

| You did… | Then update… |
|---|---|
| moved the proof forward, or changed what's next | `STATUS.md` (**always**) |
| lost time to a non-obvious trap | `gotchas.md` |
| chose a spec, invariant, or abstraction, and rejected alternatives | a new `decisions/NNNN-slug.md` |
| built understanding of some code or tooling that took real effort | a new or existing `topics/*.md` |
| anything non-trivial | append to today's `journal/YYYY-MM-DD.md` |

The `/notes` skill walks through this. There is also a `Stop` hook that will
remind you once per session if you changed `.v` files but not `notes/`.

## Conventions

- **Write for a stranger.** No "as discussed", no "the file we were looking
  at". Name files by path, lemmas by name.
- **Absolute dates.** "2026-09-11", never "yesterday" or "last week".
- **Cite the code.** `new/proof/go_etcd_io/raft/v3_proof/readonly.v:295` beats
  "the try_read lemma somewhere in readonly".
- **Record the dead ends.** A failed approach and *why* it failed is often
  worth more than the approach that worked, because the next agent will
  otherwise try it again.
- **Correct, don't append.** When `STATUS.md` or a topic note goes stale,
  rewrite it. Superseded decisions get a `Superseded by NNNN` line at the top
  rather than being deleted. The journal is the only append-only file.
- **Keep it short enough to be read.** `STATUS.md` should stay under ~150
  lines; push detail down into `topics/`.

## What does *not* go here

- Anything derivable from the code, `git log`, or CI.
- Perennial tactic documentation — that lives in
  `new/proof/PERENNIAL_PROOF_TUTORIAL.md`,
  `new/proof/PERENNIAL_PROOF_REFERENCE.md`, and the `perennial-tactics` skill.
  Note here only what those get *wrong* or omit.
- Secrets or credentials of any kind.
