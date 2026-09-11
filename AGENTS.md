# etcd-grove

This repo verifies **etcd** — starting with its Raft implementation — using
Perennial, a system implemented in Rocq for proving Go code correct. Perennial
builds on the Iris separation logic framework and uses stdpp (a Rocq standard
library for Iris). It is a fork of
[mit-pdos/perennial](https://github.com/mit-pdos/perennial); the framework is
inherited, the etcd proofs are the work.

## Read the notes first

**`notes/` is this project's persistent memory, and it is not optional.**

- Start at `notes/STATUS.md` — where the proof is, what is in flight, what is
  next. A `SessionStart` hook injects it automatically, so you may already have
  it in context.
- `notes/README.md` is the full contract; `notes/gotchas.md`,
  `notes/topics/`, `notes/decisions/`, and `notes/journal/` are the rest.
- **Before you finish, update `notes/`.** At minimum `notes/STATUS.md` plus an
  entry in today's `notes/journal/YYYY-MM-DD.md`; add to `gotchas.md`,
  `topics/`, or a new `decisions/` record when the session earned one. Run
  `/notes` to be walked through it. A `Stop` hook will remind you once per
  session if you changed `.v` files and left `notes/` untouched.

This exists so that a fresh agent with no conversation history can pick the
work up. Write for that reader.

## Layout

Most of the implementation is in `new/`, with program proofs in `new/proof/`.
The etcd work is under `new/proof/go_etcd_io/` — see
`notes/topics/raft-proof-map.md` for a guided tour.

`new/code/` and `new/generatedproof/` are **auto-generated** Goose output: do
not edit anything there, and do not use them as a model for proof style. A
change you want in `new/code/` has to be made in the Go fork and regenerated —
see `notes/topics/goose-workflow.md`.

## Proof writing

There is a tutorial: @new/proof/PERENNIAL_PROOF_TUTORIAL.md, a reference:
@new/proof/PERENNIAL_PROOF_REFERENCE.md, and notes on Iris proof mode:
@new/proof/IRIS_PROOF_MODE.md. The `perennial-tactics` skill has detailed
tactic documentation with proof-state examples.

Style conventions are in `docs/style_guide.md`.

## Building

`make ci` builds `new/should_build.vo`, which is what CI checks — a proof not
reachable from `new/should_build.v` is not being built. For a faster inner
loop use `make vos`, or a targeted `make <file>.required_vos`.
`CONTRIBUTING.md` has the details, including the `vos`/`vok` tricks.

## Tools

`etc/` holds development and CI tooling; `new/etc/` holds the Goose and Grackle
update scripts. `etc/agent-notes/` holds the two hooks that keep `notes/`
alive.
