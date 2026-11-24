---
name: dsverify
description: Prove a dsverify challenge - a Go distributed system (a replicated store, a consensus protocol) deployed over the net extension with clients on machines of their own, whose given top-level robustness statement must be proved in Lean with Perennial and Goose, spec-first - the hubs mapped and the cross-package interface (hub statements, invariants, cross-package specs) drafted, reviewed and frozen before proofs; packages then write their internal specs and prove them in parallel, riskiest step first. Use when starting or continuing work on such a challenge.
---

# Proving a dsverify challenge with Perennial (Lean), spec-first

A **challenge** is a self-contained tree (`CHALLENGE.md`): a Go
distributed system and the program that tests it (a driver machine, client machines,
server machines, over TCP), Goose's translation of it, the Lean environment it runs in (the net
extension and its specs, the remote-call library, the generic robustness statement), and one
**goal**: a top-level statement, given, with its declared premises. You prove it. The proof of the
goal must rest on Lean's three axioms (`propext`, `Classical.choice`, `Quot.sound`) and nothing
else: every premise is a hypothesis of the statement itself, visible to whoever reads it.

This skill is a method, not a library. It encodes lessons from a large verification of this kind:
most of the cost was not proving but **re-stating**: specs revised after proofs existed, because a
caller needed more, or a statement turned out false of the code. The method front-loads what causes
re-statement. The challenge's own `CLAUDE.md` is authoritative for paths and commands; where it
and this skill differ, it wins.

## The files

| file | read it when |
|---|---|
| `CHALLENGE.md` | first: what you are given, what you may change, what "done" means, the premise rules |
| `SETUP.md` | before the first edit: the layout, the kit file, Goose, the generators, modules, tiers, building |
| `NET.md` | before any spec: the network model, the remote-call library, the statement's shape |
| `TESTING.md` | before any spec: the executable test the statement is about, porcupine, the stress test |
| `SPEC-FIRST.md` | planning or running a stage: the phases and their exit conditions |
| `HUBS.md` | before the interface: the hub statements, and what to do when a statement keeps changing |
| `PRINCIPLES.md` | writing or reviewing any spec, predicate, law or invariant |
| `LIFECYCLE.md` | before proving with an object that passes between threads (pooled, queued, handed off) |
| `TRUST.md` | introducing a hypothesis, finding a bug in the target, bounding threads/counters |
| `PROOF-NOTES.md` | writing proofs: Perennial and Lean craft |
| `TOOLS.md` | the scripts the challenge has, and the ones worth building |
| `REPORT.md` | what to record per stage and at the end |
| `examples/` | specs the user reviewed, with their critiques (starts empty; add as you go) |

## The workflow

1. **Read the challenge** (`CHALLENGE.md`, the challenge's `CLAUDE.md`): the statement file, each
   premise class it names, the kit file `etc/dsv/<kit>.py`, the Go program. Build what is given
   (`SETUP.md`, "Building"); it must build before you change anything.
2. **Run the test** (`TESTING.md`): the deployment the statement is about, as Go, many times; then
   the stress test with direct checks of the protocol's invariants. Read the in-scope code for bugs.
   A bug the test can trigger is a finding (`TRUST.md`, "Findings").
3. **Scope is given; write down what it covers** (`SPEC-FIRST.md`, "Scope"): the configuration the
   program chooses, the faults the network model allows, what the statement leaves out. Do not
   narrow or widen it: the statement and its premises are not yours to change.
4. **The model and the codec, proved** (`TESTING.md`, "The sequential model"): the Go model's
   functions proved to compute the Lean model's, and the codec's encodings: the first linked
   results, small and pure, through the whole toolchain (Goose, specs, proofs, links).
5. **The hub map** (`HUBS.md`): from the code and the statement, name the statements that will
   mention many subsystems (the start lemma, each machine's main, the server's constructor, the
   protocol invariant) and give each subsystem its sealed slots before writing them.
6. **Interface → Review → Freeze → Prove** (`SPEC-FIRST.md`), per stage. The interface (hub
   statements, cross-package invariants in full, cross-package specs) before any proof; one fresh
   review round and a check of its repairs; every hypothesis you introduced attacked before the
   freeze; the freeze tagged `stageN-frozen` before Prove starts (no proof agent before the tag:
   `SPEC-FIRST.md`, "The proof gate"); then one agent per package writes its internal specs and
   proves them, its top functions first against stated `sorry`s, then the riskiest step, changing
   internal statements freely (not the invariants of objects shared across threads); every change to
   the frozen interface logged and classified. Each phase leaves its record.
7. **Done** (`CHALLENGE.md`, "Done"): the goal theorem builds, its `#print axioms` lists Lean's three
   axioms only, the challenge's checks pass. **Report** (`REPORT.md`).

## Rules that hold throughout

- **Never touch the goal.** The statement file, the premise classes it names, the definitions the
  statement is written in (the program, the deployment, the addresses) and the non-vacuity module
  are the challenge's. A goal you believe is false or unprovable is reported with the evidence
  (a failing Go test, a refuted premise), not edited.
- **No axiom, no `sorry`, no trusted code of your own** in what the goal rests on. A library spec you
  cannot prove yet may be a named hypothesis while you work (`TRUST.md`), never at the end.
- **A bug in the target gets a failing Go test** before (or with) the fix (`TRUST.md`, "Findings").
- **Do not change the framework to unblock a proof.** A limitation of Perennial, Goose or the given
  environment (the net extension, the remote library, their specs) is worked around in your own
  files (a lemma, a law derived from the given specs) and recorded in your notes as a proposal.
- **One stage, one branch, one worktree**; the main branch only receives a stage whose checks pass.
- **The user decides** freezes and changes to frozen statements, when one can answer. Ask with the
  evidence; do not decide by default. Between those points, keep going without asking. If no user
  can answer, take your recommendation and log it as your decision: the step it closes still
  happens in full.
- **A wait must be able to end.** To order background jobs, chain them in one shell (`a && b`) or
  wait on a PID (`while kill -0 $pid; do sleep 5; done`), never on `pgrep -f "<pattern>"`: the
  waiting shell's own command line contains the pattern, so the wait never ends. Before waiting
  on background work (yours or a subagent's), check that it still runs; work that was killed or
  stopped never reports. An idle session waiting on a job that cannot finish looks done from the
  outside.
- **Count the goal path's `sorry`s every round.** Three rounds without a decrease trigger a
  simplification review: a fresh agent, given the code and the statements (not the notes), proposes
  simpler invariants, designs and (where allowed, `CHALLENGE.md`) code changes, as options.
- **A placeholder is debt.** A parameter or slot fixed to `True` for now gets its content before
  proofs depend on it; every proof built over the placeholder is redone when it does.
- **"No invariant found" is not a stop.** Record what failed and try another invariant, a simpler
  design or a code change; only a hard stop (`SPEC-FIRST.md`, "Who decides") ends the work.
- **Notes are part of the work**: a `notes/STATUS.md` summary of where the work is, a
  `notes/decisions.md` of design decisions with their reasons (superseded, not deleted, when they
  turn out wrong), a plan file per stage.

## Background reading (public)

- Perennial's Lean docs, in the dependency (`.lake/packages/perennial/docs/`):
  `PERENNIAL_PROOF_TUTORIAL.md`, `PERENNIAL_PROOF_REFERENCE.md`, `IRIS_PROOF_MODE.md`.
- Chajed et al., *Verifying concurrent, crash-safe systems with Perennial* (SOSP 2019).
- Sharma et al., *Grove: a Separation-Logic Library for Verifying Distributed Systems* (SOSP 2023):
  the closest prior work; its examples are the style of top-level statement a challenge has.
- Chajed et al., *GoJournal* (OSDI 2021); Goose's own README for the translation's scope.
- Jung et al., *Iris from the ground up* (JFP 2018); da Rocha Pinto et al., *TaDA* (ECOOP 2014) for
  logically atomic specs.
- Herlihy and Wing, *Linearizability* (TOPLAS 1990); Athalye's porcupine
  (`github.com/anishathalye/porcupine`) and Kingsbury's Knossos/Jepsen for history checking.
