# Decisions (Lean port)

Why the Lean port is the way it is. Newest last. The design of the proof itself is
recorded on `main` (`notes/decisions.md`); this file only covers choices the port
had to make.

---

## The Rocq module discipline, in Lean

**2026-10-06 · accepted**

`main` gives every Go function four files (`spec_`/`postulates_`/`proof_`/`link_`)
and uses Rocq's module system for two guarantees (main's decisions.md,
2026-09-14 and 2026-09-18): one Hoare triple per Go function, a duplicate being a
build error (`Include` of two signatures with the same label), and a proof that sees
only the *specs* of its callees, never their proofs (opaque ascription), which also
keeps the proofs checking in parallel.

**Decision:** per Go function, `Spec/<fn>.lean` holds `def <fn>.spec : Prop` (the
triple, with its binders); `Proof/<fn>.lean` holds
`theorem <fn>.wp_proof (h₁ : <callee₁>.spec) … : <fn>.spec`, importing only its
callees' `Spec` files; `Link.lean` instantiates each proof with its callees'
results. Lean's global names make a second `<fn>.spec` a build error (the first
guarantee); taking the callees' specs as hypotheses, with only their `Spec` files
imported, is the second. The `postulates_` file becomes the hypothesis list.
Trust-boundary triples are `axiom <fn>.wp_proof : <fn>.spec` and unfinished ones
`sorry`, so `#print axioms` on a result separates them as `main` does with
`Axiom`/`Admitted`.

**Rejected — one file per function holding spec and proof.** Then a caller imports
its callees' proofs, which both exposes them and serializes the build.

## Build timing: a `lean` shim behind a copy of the toolchain

`etc/build-report.py` (the counterpart of `main`'s, which reads what `etc/rocqc.py`
records around each `rocq compile`) needs each module compile's start, end, CPU,
peak memory and exit status. Lake prints only a duration per job, after the fact,
and has no hook around the compiler; it runs `<sysroot>/bin/lean`, with the
sysroot from `LEAN_SYSROOT` when `LAKE_OVERRIDE_LEAN` is set.

**Decision:** `build-report.py build` makes `.lake/build-report/sysroot/`, symlinks
to the real toolchain except `bin/lean`, a shim that runs the real `lean` under
`wait4` and appends one JSON line per compile to `.lake/build-report/<build>.jsonl`;
then it runs `lake build` with those two variables set. Lake's traces do not
depend on the `lean` path (checked: an up-to-date build stays up to date under the
shim), so the shim changes timing only by Python's start-up per compile. The
imports come from the `.setup.json` Lake writes per module (`importArts`: the
transitive imports; the last of them to finish is always a direct one, so the
critical path and the unlimited-cores bound come out the same as with direct
imports).

**Rejected — timestamping Lake's output.** `✔ [n/m] Built M (12s)` gives an end
time (when the line is read) and a duration, but not CPU or memory, and the line
can lag the compile's end.

Lake runs at most one compile per core: in the first full build of this
repository's modules on 24 cores (2026-10-08), 46s ran exactly 24 compiles and
none ran more. So the report treats the cores as Lake's job slots ("all slots
busy"), and "idle" on the critical path is a wait for a free core, Lake's own
work between compiles, or its start-up. Lean also elaborates a module's
declarations in parallel, so the report charts cores busy (each compile's CPU
spread over its run) next to compiles running.

## Many people's agents, coordinating through `lean`

**2026-10-08 · accepted** (the people running the project decided: agents push
directly to `lean`; `lean` is the primary development; no per-person limits on
agents)

Several people run agents continuously on VMs watching this repository. Big ideas go
between people and agents through files (`manual-notes.txt`, `notes/chat/`); small
questions stay with each agent's own operator.

**Decision:** `notes/collaboration.md`. In short: git on `origin` is the only shared
medium and a push race the only lock; one file per task (`notes/tasks/`) and per chat
thread (`notes/chat/`); `etc/tasks.py` changes them by committing that one file on top
of a fresh `origin/lean` and pushing straight to `lean`, retrying on a lost race;
liveness is pushes to the task branch, so `lean` carries no heartbeat commits;
`etc/land.py` is the one way to land work (rebase, regenerate `Link.lean`, build,
TCB check, push), except that protected paths (`etc/protected-paths.txt`) go through a
PR a person merges, and CI (`board.yml`) fails a direct push that changed one.
`etc/gen-link.py` now reads the callees from the Lean proofs' hypotheses instead of
the Rocq `postulates_*.v` (same output), since the Rocq is no longer followed.

**Rejected — every landing through a PR with auto-merge.** Claims, chat and notes must
be pushed directly anyway; a user-owned repository has no merge queue, so "require up
to date" would turn each landing into a rebase race in GitHub's UI; and gating only
what changes the trust base or the claims puts people's attention where it counts.

**Rejected — GitHub issues or discussions for tasks and chat.** They would put the
coordination outside the repository, invisible to agents of other tools and to
offline readers, and make the board depend on a token on every VM.

**Rejected — one shared journal and a generated questions file.** With many agents an
append-only file in one place is a permanent merge conflict, and a generated file
committed on every state change churns `lean`; task logs, chat threads and
`etc/tasks.py status` (printed, and on each `board.yml` run's summary) replace them.
