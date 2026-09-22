# etcd-grove

This repo verifies **etcd** — starting with its Raft implementation — using
Perennial, a system implemented in Rocq for proving Go code correct. Perennial
builds on the Iris separation logic framework and uses stdpp (a Rocq standard
library for Iris). It is a fork of
[mit-pdos/perennial](https://github.com/mit-pdos/perennial); the framework is
inherited, the etcd proofs are the work.

## Read the notes first

`notes/` is this project's persistent memory: plain markdown, committed, no
tooling.

- Start at `notes/STATUS.md` — where the proof is, what is in flight, what is
  next, what is known broken.
- `notes/README.md` lists the rest and gives the conventions.
- **Before you finish, update the notes.** At minimum `notes/STATUS.md` if
  anything moved, plus a dated entry appended to `notes/journal.md`. Add to
  `notes/gotchas.md`, a topic file, or `notes/decisions.md` when the session
  earned it.

Nothing enforces this; it is deliberately on you. The point is that a fresh
agent with no conversation history can pick the work up — write for that
reader.

## Layout

Most of the implementation is in `new/`, with program proofs in `new/proof/`.
The etcd work is under `new/proof/go_etcd_io/` — see `notes/raft-proof-map.md`
for a guided tour.

`new/code/` and `new/generatedproof/` are **auto-generated** Goose output: do
not edit anything there, and do not use them as a model for proof style. A
change you want in `new/code/` has to be made in the Go fork and regenerated —
see `notes/goose-workflow.md`.

## Proof writing

There is a tutorial: @new/proof/PERENNIAL_PROOF_TUTORIAL.md, a reference:
@new/proof/PERENNIAL_PROOF_REFERENCE.md, and notes on Iris proof mode:
@new/proof/IRIS_PROOF_MODE.md. Style conventions are in `docs/style_guide.md`.

## Building

`make ci` builds `new/should_build.vo`, which is what CI checks — a proof not
reachable from `new/should_build.v` is not being built. For a faster inner
loop use `make vos`, or a targeted `make <file>.required_vos`.
`CONTRIBUTING.md` has the details, including the `vos`/`vok` tricks.

**Auditing is two separate commands**: `make` first — that is the only thing
that checks the proofs — and then `etc/tcb-report.py`, whose entire job is to
check what the build cannot (that the statements say what was meant, that an
axiom set is not satisfied trivially, and that nothing is silently outside
the build). Neither substitutes for the other; see
`notes/tcb-accounting.md`.

## Adding tooling

Only add structure — a script, a hook, a generator, a directory hierarchy —
where there is a demonstrated benefit. Prefer a sentence in a markdown file
over a mechanism, and prefer a mechanism no particular coding agent is required
to understand. See the second entry in `notes/decisions.md`.

## Tools

`etc/` holds development and CI tooling; `new/etc/` holds the Goose and Grackle
update scripts.
