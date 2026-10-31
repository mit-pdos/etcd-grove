# Plan: a skill for autonomous, end-to-end verification of a Go package

Status: proposed (2026-10-30, branch `worktree-autoverify-plan`); revised the same day after four
independent reviews (soundness, feasibility, history, methodology: "Reviews" at the end says what
each changed). Nothing built yet. Written from the history of this repository (3.4k commits on
`lean` since 2026-10-06, the Rocq development on `main`). It builds on `notes/spec-first-plan.md`
(whose steps it automates) and the `spec`, `axiom`, `progressive-verification`, `proof-perf` and
`proof-cleanup` skills (which it calls).

## Goal

Given a Go package (or a few that form a system: raft; a server over raft) and a Go test of it, run
**without a human in the loop** to a closed theorem about the test's program, linked through proofs
of the package's code, with a trust base that is reported, tested and adversarially reviewed. The
human's part is to audit at the end, if they want: the Go test (the top-level spec), the trusted
surface (below), and the `issues/` found. Nothing during the run waits for them.

Two user decisions (2026-10-30) fix the shape:

1. **The top-level spec is the adequacy theorem of a Go test**: the statement to audit is Go code
   that anyone can read and run (`examples/kv`'s `Main` with porcupine's check) plus Perennial's
   adequacy theorem. Every closed theorem the repository has is of this form (`notes/STATUS.md`,
   "The closed theorems").
2. **Autonomous.** Every decision the user took during the stages so far (eight in M2's first day:
   scope, design options, axioms, fork fixes, merge order; `notes/spec-first-plan.md`, "Who
   decides") becomes a gate: a mechanical check, a fixed rule, or an adjudication by fresh agents
   with mechanical evidence. The rules that kept the work sound under a human (no statement
   weakened, no family of specs, the trust base not growing silently) become hard checks, run
   against the run's starting state, by tooling the run cannot change.

**What the theorem says, exactly.** For every real execution of the program (the package
initialization, then `Main`) of `n < 2^63` steps from a fresh state with one thread: every thread is
a value or can step, none ended in a panic, and *if* the main thread has finished, its result is as
stated. It is **partial correctness**: Perennial's locks are spin locks (`Golang/Theory/Lock.lean`),
so a blocked thread keeps stepping; a program that deadlocks, or a server that never answers, before
the check satisfies the theorem. The report states it that way ("no panic; if `Main` returns,
porcupine said `Ok`"), and the gates below count a hang as not excluded.

**The deliverables, three levels** (the test is the anchor, not the only claim):

- (a) *the driver theorem*, generated, for `MainWith(cfg)` over every bounded configuration
  `cfg` (nodes, clients, operations, keys, fault seed), not one fixed size; `Main` is the instance
  the Go test runs. It is what a human audits and what shows (b) and (c) satisfiable.
- (b) *the library-level theorem* the driver is an instance of: for a porcupine driver, `Run.spec`
  (`Spec/.../lintest/Run.lean`) instantiated with any generator and stated as a Lean theorem whose
  post includes `Linearizable` of the recorded history, which takes porcupine's soundness out of the
  trust base.
- (c) *the exported API specs* (`etc/api/<pkg>.txt`, the generated `interface/`): logically atomic
  triples, the claim about every other client. For a protocol, also the pure safety theorems over
  `Step` (election safety, state-machine safety): short, readable, comparable with TLA+ or IronFleet.

**Push-button** means: the input is a pinned Go revision, a test, and the run's fixed parameters
(the deployed configuration, the mutation operators and thresholds, budgets); the output is a branch
with the theorems, the report, and the issues. A run may stop short (a `sorry` left, an axiom refuted
and not replaced, a Go bug its gates did not let it fix) and then it says exactly where.

## What the history says (the evidence the plan rests on)

Each point is a rule below; the sources have the details.

**Specs.**
- Spec churn is the main cost, and it is not falsity: of 64 sampled revisions of existing specs, 23
  were a caller needing more and 20 a scope widening; 3 were false behavior
  (`notes/spec-first-plan.md`, step 1). `raft__Step` was revised 48 times, almost all widenings. So:
  fix the scope first (the test does), draft every spec top-down, prove the glue before the bodies.
- Reviews before proofs find most spec problems (the compactor: 18 of 19 first-tier revisions from
  fresh-reviewer rounds; the 19th from glue); repairs introduce defects. The freeze leaked once,
  through a caller that did not exist yet: freeze only when every caller's glue proves.
- Review depth has to match how new the abstraction is. raft's unified node API (Storage,
  Ready/Advance, snapshots, reconfiguration; `notes/raft-unified-plan.md`) took 11 review rounds to
  freeze, then had its storage contract redesigned after the freeze; of its 162 changes after the
  freeze, classified (`notes/spec-first-plan.md`, "The change log after the freeze, classified"),
  140 were real and 59 of those (about 40%) were fixes and redesigns review had missed, against 36
  conformance edits and 12 adaptations of callers. Eight of the fixes were facts of the Go code no
  review saw and proofs found: `MemoryStorage.InitialState` unlocked, `newRaft` reading
  `FirstIndex`/`LastIndex` before `InitialState`, `Restore` needing `Restorable`, a bare
  `MemoryStorage`'s empty `ConfState`, a new leader's commit index lagging a snapshot, an empty
  `ConfChangeV2` against etcd's `apply` panic, the concurrent `ApplyConfChange`, `run` panicking on
  a `Snapshot()` error. All are about the order, thread or state in which Go calls an interface the
  library calls back, which a protocol trace does not show.
- Mode families are the most expensive mistake: auth's on/off copies, about 7k lines, every other
  track editing both (`notes/auth-mode-merge-plan.md`). One spec per function; a mode is state.
- Unproved triples are unchecked claims ("an `Admitted` is not a placeholder for work",
  `main:notes/false-statements.md`); placeholder axioms written by one track drifted from the
  statements another proved (D22 S8c's W3, reverted `72a1cb065b`).

**The protocol layer** (raft; `Proof/go_etcd_io/raft/v3/Protocol/`, 21k lines).
- What worked is a *permissioned state machine* in three layers: Go heap ↔ physical node state
  (`ownRaftPhys`), physical ↔ protocol state (a pure relation), protocol state ↔ ghost knowledge
  (`ownRaftGhost`). A per-node `Step` relation of plain values whose rules mirror the Go transitions,
  reflexive and transitive (one Go function that takes several steps refines one `Step`), the outbox
  in the state with a drain rule. Node-local ghost authority; everything a step learns is persistent
  knowledge carried on the message (`isMessage` by cases on the message type), so delay,
  duplication and reordering cost nothing; election safety is the agreement of two persistent facts.
  One ghost update (`ownRaftGhost_step`) at one dispatcher; every spec below it a physical triple
  with a pure `Step` witness, which made widenings mechanical (B7: about 40 branch files, 8000
  lines, converted by recipe in a day).
- The one global invariant (`raftCommitInv`) was forced, found by stating the safety theorems early
  as admitted lemmas: two nodes' local state could not prove them.
- For a hard widening (reconfiguration): paper proof → adversarial review against the Go code →
  small explicit-state checker with planted bugs → Lean model and invariants rule by rule → ghost at
  the old scope → general case → code. The review found the read-index bugs fixed upstream
  (raft#535, #536); the checker found no new bug but validated fixes and gave minimal traces.
- Widening is cheap behind a single hook (`CfgAt`: one lemma, three uses) and expensive when
  messages lack fields (`Msg` had only `voters`; snapshots, D22: 188 commits) or knowledge belongs
  to the application (snapshot contents).
- False statements at this layer were claims about Go never checked against it (term wrap,
  `None = 0`, the empty voter set's majority, `AppOk`'s commit index): nine of ten in main's table.

**Proof engineering.**
- Effort split (Rocq, `main:notes/proof-effort.md`): tactic trial and error about 50%, reading
  generated code 20%, ownership plumbing 20%, the protocol argument 10%. The incremental checker
  (`etc/lean-check.py`, built three weeks in) is the biggest lever and must exist from day one. A
  worked example beats prose (a gotcha's prose version "was read and misapplied").
- The per-function spec/proof/link discipline made parallel proving and the retarget work: the
  whole Rocq raft proof was ported in about three days by parallel agents over fixed statements.
- Performance is a property of proof patterns: targeted dispatch (`raft__Step/Dispatch.lean`: 5223
  s → 1250 s CPU), `wp_join` after a case split (911 s → 63 s), loops given only what they read,
  framing by name. Flakiness came from global state in tactics; silent admits from `wp_apply … $$
  [frames]` (only the "declaration uses `sorry`" warning shows them); an agent reported a Rocq proof
  done that `.vos` never checked (`main:notes/journal.md`, 2026-09-16), as `--fast` skips the
  kernel here.
- Re-verification (raft v3.7, 139 functions changed): the pure model survived as a rename; the
  physical predicates took the bulk (R4/R5, about 32k lines); a parallel tree kept the trunk green.
- Parallel provers duplicate helpers (about 10.5k copied proof lines, 4.4%,
  `notes/auth-mode-merge-plan.md`; `notes/dedup-plan.md`).

**The trust base.**
- 766 axioms today; 47 known to have been false, mostly found by reading after proofs rested on
  them (`notes/audit.md`; one stayed false 9 days, one 11). Three were inconsistent in Lean
  (quantified over a semantics instance). 31 of 44 *have* a refuting Go execution; the spec-guided
  tester, run only on bbolt so far (`etc/spec-test/bbolt`, about 25 lines of Go per axiom), refuted
  every false bbolt row with no false alarm in 10 000 runs; the `axiom` skill refuted two more with
  a sorry-free Lean proof next to a panicking Go program (`examples/axiomcx`).
- Not every trusted statement is an axiom: typeclass hypotheses of the closed theorems
  (`log.NewModel`, a hand-written `FuncUnfold`; `ContextReadErrs`, `PeerPausable`, about ten) are
  invisible to `#print axioms` and `etc/tcb-report.py`; `TrustedCode/` models, GooseLang extensions
  and names-only translations are trusted too.
- Proofs narrowed scope from inside: D19m-p removed axioms by making branches unreachable (`run`'s
  exits a bag with predicate `False`: no shutdown covered; the lessor's grant guard `False`: no
  lease expiry; one member, `%Hone`: `MsgSnap` dead). Nothing in the configuration showed it.

**The drivers** (`examples/`, the closed theorems of `notes/STATUS.md`).
- The clean tier (`lintest`'s counter and logkv family, `kv_porcupine_safe`,
  `kv_witness_porcupine_safe`) takes no Iris premise: about 100 lines of Go and a 15-line theorem
  (plus `log.NewModel`). The server tier (`putget_safe` through `k8setcd3_safe`) takes `premises`,
  assumed Hoare triples, and those were false twice: `∀ n, rnStopOk n` (D19r) and its replacement
  `rnStopOkStarted`, still open (`notes/raft-spec-review.md`, "High 1"), which makes every server
  theorem vacuous today.
- Building a closed driver is the vacuity check that worked (raft's `isLogger`; the workload clause
  a delete-then-put transaction refutes, D19c; the feature-gate contract), but only for pure
  premises.
- The drivers are weaker than they look: every etcd driver returns without checking on an error
  (`putget`'s `if err != nil { return }`); `k8setcd3` skips porcupine after a failed write; the kv
  cluster's transport drops message types raft's spec does not cover; the in-process transport
  shares cells across nodes, so the codec (`raftpb` marshalling) is outside every theorem. The
  DaemonSet `Main` is false of its code (D51: fails 2 runs in 100); D51 kept it deliberately, so the
  proof would show where it gets stuck.
- Environment models are specs too: D50's "a failed write had no effect" was withdrawn by D51 (the
  API server can commit and still return an error, `AmbiguousWrites`), and that is the bug's path.
- With porcupine, the proved spec is completeness only (`Linearizable → r ≠ "Illegal"`,
  `Spec/github_com/anishathalye/porcupine/CheckOperationsVerbose.lean`); `Ok` implies linearizable
  is trusted, and depends on each model's `Equal`/`Hash` agreeing (kv's `Hash` drops `""` entries).
- Calibration (`notes/logkv-eval-summary.md`): a fresh agent proved an 84-line concurrent program
  end to end in about 112 minutes (344 spec lines, 1316 proof lines); each one-feature variant in 8
  to 19 minutes.
- Not covered by any driver theorem: crashes, liveness, a network outside one process (the network
  is the `Transport.Start` axiom; no distributed adequacy in the Lean port, D21a).

**Bugs found.** About 30 by writing specs, about 30 by proof attempts, about 18 by designing a stage
(listing what a function writes), about 9 by adversarial review (the highest value per finding),
few by running things, none new by model checking. Of about 155 findings, 34 became `nonissues/`
(preconditions etcd already meets) at the user's review of 2026-10-23, among them a fork fix that
passed its own regression test (`AuthInfoFromTLS`, D19l); two cache fixes made only for provability
were reverted (the user's rule, 2026-10-09: no change to etcd's code unless it fixes a bug).

**Process.** Bottom-up units gated after each; contract-first axioms at the frontier (replaced later
without changing callers only when both sides agreed the statement first: D22 W3); an inventory
before a redesign; static case first, dynamic as an extension; temporary premises named and
grep-able. Failures: a stage branch that became the trunk; specs proved before anyone checked they
were satisfiable; long sub-stage chains each adding a variant; agents drifting to proving and
deleting finished proofs (M2's S1 agent re-proved about 45 files); agents sharing scratch
directories, `git add -A` sweeping scratch into commits, rate-limit deaths leaving unverified files,
OOM kills from parallel builds (`main:notes/journal.md`); `sorry` stubs with no callee hypotheses
hiding axioms from a collection's baseline (M2, `dbc8fb404c`).

## The trusted surface and the run's invariants

Under a test-adequacy theorem with pure premises, no internal spec can make the theorem false; only
the trusted surface can. So the run's soundness is the integrity of that surface, enforced by
tooling the run does not control.

**The trusted surface**: the driver and its Go model; the closed theorem's statement and its
binders; the axioms; the typeclass hypotheses; `TrustedCode/` models, GooseLang extensions
(`GooseLang/Ext/*/Impl`), names-only and trusted entries of the Goose configuration; environment
models (an API server, a transport); the pins (Perennial, Lean toolchain, Go toolchain, the
project); the fork's diff from upstream; Perennial, Goose and Lean.

**The run's invariants** (hard; a breach fails the run):

1. *An immutable path set*, fixed at Stage 0's exit: `etc/` (the gate scripts, `tcb-baseline.txt`,
   the collections, `proof_roots.py`, `api/*-layout.txt`), `.claude/skills/autoverify/`,
   `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, the driver and its model (hashed). A
   change to the Goose configuration (`Code/**.toml`), `TrustedCode/`, `GooseLang/Ext/` or a
   hand-written `FuncUnfold` model after Stage 0 is a thaw that goes through Stage 4 (the model
   tested against the Go body; the body-first rule reads the Go source, not the translation).
2. *Every gate compares against the base commit*, never against what the run last wrote: no
   `--check --update`, no regenerated baseline, fingerprint or interface accepted as the reference.
   The report shows each delta (new axioms, new hypotheses, thawed statements).
3. *Allowed binders*: a Lean meta-check on each closed theorem's type admits exactly
   `GoGlobalContext`, `GoLocalContext`, `go.Semantics`, the Goose-generated `<pkg>.Assumptions`,
   `IsInit`, `threads = 1`, the step bound, and named pure premises with a satisfiability witness.
   Any other hypothesis (a class such as `log.NewModel`) counts as an axiom: Stage 4, listed first.
   **No Iris premise at the top** (stricter than D19a, which let `rnStopOkStarted` in).
4. *No Lean bypass*: a lint bans `debug.*` options (`debug.skipKernelTC`; `Proof/AbstractBullets.lean`
   documents it), `run_cmd`, `addDecl`, new elaborators, macros or `elab_rules` in proof files
   (outside a reviewed allowlist); the final audit replays the result modules with `lean4checker`.
5. *The program term is generated*: the theorem's program is exactly the generated initializer then
   `Main`/`MainWith` (today `Adequacy.lean` is hand-written, `kvProgram := initialize' #() ;; Main
   #()`; a hand-written term could be anything).
6. *Scope narrowed inside proofs is reported*: every predicate, guard or bag instantiated to `False`
   or `True` (the D19m-p pattern) is listed as a scope restriction; the driver runs with Go coverage,
   and a branch the Go runs reach but the proof treats as unreachable is a false premise and fails
   the gate.
7. *Fork diff bounded*: the verified code is "upstream @rev + an N-line diff"; the first line of the
   report says so; each hunk has a gated issue (Autonomy, below).

**The final audit** (Stage 6, a fresh job): a fresh clone at the run's last commit; the immutable set
restored from the base commit (any difference fails); a clean `lake build` with no cached `.olean`;
`etc/tcb-report.py` delta against the base commit's baseline; the binder check; the bypass lint;
`lean4checker`; the driver gates re-run.

## The top-level spec: a Go test

**The driver.** `MainWith(cfg)` and `Main` (in `examples/<name>/`) build the system as deployed and
run a randomized workload, checking the outcome in Go and panicking on a violation:

- *linearizability*: a history recorded by the clients, checked by porcupine against a sequential
  model in Go (`examples/lintest`'s `Run(model, apply, gen, clock, clients, ops)`, whose `applySpec`
  makes any logically atomic library a porcupine example);
- *safety invariants*: assertions on observed state (watch events exactly the writes, `watchkv`; at
  most one pod per node);
- *environment*: the faults to tolerate are drawn by the driver (drop, duplicate, reorder,
  partition, crash-stop and restart from durable state), from `RandomUint64`, so the theorem holds
  for every schedule. The driver's transport is verified Go, not an axiom, where possible
  (`linkv3p` cuts and mends links); messages go through the real codec, or the codec is listed as
  unverified.

The driver is Goose-translatable (flat input and output structs, so the model decodes purely;
`linkvtxn`). Proof artifacts inside it are limited to a whitelist of Perennial primitives that are
no-ops in Go (prophecy resolution), so they cannot hide an early return from the lints.

**Inputs fixed before the run** (not the run's reading): the deployed configuration to diff against
(for raft under etcd: etcd's server sets `CheckQuorum` and `PreVote` on, which raft's own `Config`
leaves off), the mutation operators and thresholds, the run counts.

**The driver gates** (before any proof; in the skill, not tunable by the run):

1. *It runs green in Go, under stress*: exactly the translated `Main` (not a test variant), many
   runs with `-race` and with a controlled-scheduler mode exploring interleavings (goroutine
   scheduling is not seeded: 100 seeds find a 2%-rate bug only about 87% of the time, so the count is
   runs under stress, set by the skill). A failing run is a Go bug or a wrong model: an `issues/`
   file with the failing run as reproduction, then the fork-fix gate decides. Unlike D51, an
   autonomous run does not prove toward a theorem Go refutes unless the fix lands; without it, the
   run may still prove the rest and report the stuck point.
2. *It never gives up silently*: no early return on an error; a failed or timed-out operation is an
   indeterminate output porcupine checks (`linkvtxn`'s `Output.Err`). Lints: every `return` on an
   error path flagged; the driver panics unless the result is exactly `porcupine.Ok` (`Unknown` from
   a timeout is a failure, since the spec gives `Ok` only at `dur ≤ 0`). The count of checks reached
   per run is measured; a check most runs skip is reported.
3. *It catches mutants*: mutants generated by a tool over every reached function, with the skill's
   operators (flip a comparison, drop a persist, skip a quorum check, reorder an unlock, always
   return an error, always return the initial value). **A mutant is killed only when the check
   panics**; one that only hangs or times out is a survivor of the theorem (partial correctness).
   Each survivor is classified (out of scope, equivalent, a driver weakness) in the report.
4. *Its model is strict*: a fresh agent writes, from the package's documentation, illegal histories
   the model must reject (a stale read, a lost write, a duplicated apply), and a differential test
   against the upstream model where one exists (etcd's robustness model; `linkvtxn` did this). The
   model's `Equal`/`Hash` are checked to agree on random states.
5. *It reaches the code*: adequacy coverage (the `Link.lean` theorems a closed theorem reaches) is
   every function the run claims verified; a function proved but unreached is reported as unaudited.
6. *It is the deployed configuration and general*: the configuration diff against the fixed input;
   a filtering transport (the kv cluster's `deliverable`) or a bound kept only for the proof
   (`ticks`) is a listed restriction. A lint rejects a driver constant (a literal id list, a length)
   in any spec under `etc/api/`.
7. *Environment models carry their failure semantics*: an environment model (API server, storage,
   transport) is in the trust base with its deviations listed, and includes ambiguous outcomes
   (committed but errored, timed out after commit).

Several drivers per system are fine (a kv workload, a partition schedule, a watch); each is a
theorem. Upstream tests are sources, not drivers: raft's `datadriven` tests need file I/O, `fmt` and
golden files, and say only "the output equals a transcript"; etcd's robustness tests fit better,
rewritten into translatable Go as `linkvtxn` did. A run given no test writes one (the given test is
then the documentation plus the upstream tests); that driver passes the same gates and is flagged.
A soft gate failure (2, 3, 6) on a *given* driver lets the run write an amended driver, proved
alongside the given one and flagged; a hard failure (1, 7, the binder check) stops the run before
any proof.

**Out of reach today**: crash semantics beyond a simulated crash-stop and restart in one process
(torn writes, fsync order: Perennial's Rocq crash stages are not ported), liveness, a network
outside one process (Grove-style distributed adequacy: a Perennial change to request). Timing
assumptions (leases, `ReadOnlyLeaseBased`) need a clock model with bounded drift that Perennial does
not have.

## Scale: tiers

Stage 1 classifies the target; the tier picks the stages.

| tier | target | stages | example |
|---|---|---|---|
| S | sequential or lock-protected, no new axioms | 0, 1 (light), 3 (one review round), 5, 6 | the logkv family |
| M | concurrent (goroutines, channels), or new trust-boundary axioms | adds the concurrency templates, Stage 4, mutation testing | `pkg/wait`, the cache, the btree |
| L | distributed (state other nodes read through messages) | adds Stage 2 | raft, a replicated store |

Costs by tier, from the history: S, about two to three times the 112 minutes of the hand proof
(review, freeze, probes, cleanup, report); M, a day to a few; L, weeks for a raft-sized system
(reconfiguration's B1-B8 took days after weeks of groundwork; the v3.7 retarget 32k lines). Each run
has a hard token and wall-clock cap as input.

## The pipeline

Each stage has an entry condition, its work, and an exit gate that is mechanical. Within a stage,
work fans out to agents over fixed statements.

### Stage 0: set-up (once per project)

- A Goose project (pinned revision, `GO_TOOLCHAIN`, `-lean-root`), its configuration, the
  translation, `--check` in CI; the examples' `go.mod` replaces match the pins (or the Go test runs
  other code than the translation).
- Registrations of the run (Goose project, link mode, `gen-init.py`'s special packages, the TCB
  collection) in one per-run file (`etc/runs/<run>.toml`) that the scripts discover, so no shared
  table is edited and tracks never conflict on one.
- The layout, modules, package API lists, generated initializers, generated links with callee lists
  derived from the `wp_proof` hypotheses, the statement fingerprint of the roots (with a `--roots`
  mode for one result), `etc/timed-build.py`, `etc/gates.sh`; for data-heavy APIs, deep ownership
  (`etc/gen-k8s-deep.py`): a real start-up cost of a new system, budgeted.
- The Perennial pin and the base commit are frozen for the run; `lean` is merged only at stage
  gates, with a porting budget (merging `lean` once brought three Perennial pins to port).
- A Perennial checkout of the run's own at the pin (`/shared/perennial-<rev>`, built once) and a
  manifest copy pointing at it, passed to every `lake` command (`--packages=<file>`): worktrees
  share `.lake/packages`, so a plain `lake` command at another pin checks the shared Perennial out
  under every other session (it happened four times, 2026-10-23 to 10-30). `etc/lean-check.py`'s
  workers run `lake setup-file` without `--packages` and move it too: fixed before the first run. A
  gate checks the shared checkout's revision before and after each build.
- `.lake/build` seeded from a *fresh* build (stale `.olean`s gave false proof failures on modules
  that build: "unknown hypothesis", "the goal is not a WP"), by a real copy (`cp -a`, about 16 GB:
  `/shared` has no reflink), never hard links (`cp -al`: Lake rewrites `.trace` and `.setup.json` in
  place, and corrupted the source build). Never a build in the main checkout (it blocked other
  sessions). A machine-wide memory budget fixes the number of `lean-check` servers (each holds the
  prelude, 2-3 GB; three sessions were OOM-killed by parallel builds), and a disk budget the number
  of seeded worktrees (several copies landing together filled `/shared` to 98%).
- Exit: the translation builds; the *stuck-code smoke test* over the driver's call graph (`wp_auto`
  each function to its end or its first stuck point: `IndexRef` on an array value) passes, or the run
  aborts early with the gaps in `notes/perennial-changes.md` (a Perennial gap on the driver's path is
  otherwise found after a full design; the k8s surveys found ten in two days). Translator or tactic
  fixes (never axioms or model assumptions) may come from an unlanded Perennial branch through
  `lake build --packages=<file>`, the theorem then reported as conditional on that branch.

### Stage 1: inventory

- The call graph from the drivers down (`etc/k8s-worklist.py` and `etc/k8s-callgraph` already do
  this for k8s: a VTA call graph from `Main`, each function body/trusted/names-only/untranslated,
  callbacks marked; to generalize), each function classified: pure, sequential with heap,
  lock-protected, channel/goroutine, protocol step, trust frontier; the tier.
- For a re-verification: the function-level diff against the proved revision, each proof file
  classified as the retarget's R0 did, the cheapest path measured before the plan is fixed.
- Exit: `notes/<run>/inventory.md` (generated) and the task list.

### Stage 2: protocol design (tier L: the permissioned state machine)

1. *The model*: `PState` (plain values), `Step id s recv s'` with one rule per Go transition,
   written while reading the generated body; reflexive and transitive; outbox in the state, a drain
   rule; messages with every field the Go message has; each varying parameter (the configuration)
   behind one predicate with one lemma. `Step` is **executable** (decidable rules), so that:
2. *Trace validation*: traces of the Go code (raft's `state_trace.go` hook, the one its TLA+
   validation uses, `tla/`; an equivalent hook elsewhere), from the upstream tests and the driver,
   replay against `Step` before any ghost design. This is the gate that checks the model against Go,
   where nine of ten false statements were.
3. *The safety theorems* stated over the model as admitted lemmas, with the invariant they need and
   a paper proof.
4. *Adversarial review* of the model and paper proof against the Go code, by a fresh agent told to
   find a Go execution that breaks a rule or a lemma.
5. *Model checking over the same `Step`* (not a hand transcription in another language), with
   planted bugs it must find; optionally, a refinement of `Step` to the upstream TLA+ spec
   (`etcdraft.tla`), so the result is stated against a spec the community reviews.
6. *The ghost design*: node-local authority, persistent knowledge, `isMessage` by message type, a
   global invariant only where step 3 showed local state cannot prove the theorem; the allocation
   lemma at once; the one ghost update lemma.

Exit: the model and statements reviewed (every finding with a mechanical resolution), the traces
replay, the checker finds its planted bugs, the safety lemmas admitted under names. Their proofs
(and the invariants rule by rule, which find model errors: `AppCommitEq`) are Stage 5's first,
highest-priority track: the closed theorem can be stated before they are done.

*Beyond raft's shape.* The pattern generalizes where messages carry monotone knowledge (Paxos
promises and accepts, votes). Chain replication and primary-backup rely on FIFO delivery (a FIFO
transport contract, per-channel order as ghost state); leases need a time model. "One dispatcher" is
an accident of `raft.Step`; the general shape is one ghost update per message handler. A reusable
library (`Proof/PSM/`: `Step` and its closure, `Know : Msg → Prop` with a generic persistent
`isMessage`, per-node authority with `alloc` and `step` lemmas, an optional global-invariant slot,
transport contracts as parameters, the executable checker and trace replay) is built by refactoring
raft onto it, then instantiated for a Paxos-like case, before it is called a template.

For a concurrent (not distributed) package (tier M), the design is the lock invariants and the
linearization points: an atomic update in the triple (TaDa style: the library's specs take and give
back ghost state the client owns; no caller-supplied predicate as a parameter), thread tokens for
goroutines, persistent contracts for concurrent callers, tokens for once-only resources
(`.claude/skills/spec/PRINCIPLES.md`, "resources"). The designs that recurred become templates
(`briefs/concurrency.md`, each pointing to a worked proof file, not described in prose):

- *helping through the lock invariant*: the writer leaves its atomic update in a pending slot, the
  applier fires it at the linearization point, the result returns through a saved proposition keyed
  by a mono-list index; slots split done/pending at `applied` (`examples/lintest/logkv`, the kv
  store, the server's request path);
- *one-shot handoff*: a buffered(1) channel, at most one send then close, two half-owned ghost
  variables (`cache/v3/Handoff.lean`, reused by `pkg/v3/wait`);
- *`Once` with a lent resource* (`OnceFrame`), *broadcast epochs* (`InvNotifier`),
  *producer/consumer halves* (`InvWatcher`), *slots beside an RWMutex* (`InvDemux`);
- *thread tokens* for every goroutine and wait group, *time receipts* for every counter that could
  overflow;
- each part of an invariant a named predicate with read and update lemmas, never destructured by
  position (half of logkvsnap's changed lines were that).

### Stage 3: the spec skeleton, top-down

From the driver down, every function's spec in its `Spec/` file, every proof a `sorry` stub **that
takes its callee hypotheses from the Go call graph** (a lint checks the hypotheses against the
callees the body calls; a callee-free stub hides axioms and breaks derived links), axioms at the
trust frontier, `Link.lean` generated, the closed theorem stated and building. Building over stubs
checks no precondition: only proved glue does.

- *Glue proved*: every caller whose body only threads state, from the callees' specs, in full
  separation logic (most caller needs were resources: a fraction lent, a token threaded).
- *Probes*: one easy and one hard body per package, and **every constructor or allocation function
  on the path** (a precondition nothing can establish, an `isServer` no code makes, shows only
  there).
- *The tester on stubs*: the spec-guided tester (Stage 4) runs on the decidable part of every
  `sorry`'d spec of the package's own code as well, before the freeze; the Rocq tells are grepped (a
  write the spec does not own, a pointer receiver whose fields are not owned).
- *Hard rules as lints*: one spec per function (no second triple, no suffixed family beside an
  unsuffixed one); no cross-package unfold in glue; locality.
- *Error meanings*: every error return of an exported function has a stated meaning in its spec
  ("did not take effect", or "may have taken effect": an atomic update that may or may not commit),
  so a driver can record it as indeterminate soundly; a new `spec` principle.
- *Shared statements first*: a function one track axiomatizes and another proves has its statement
  agreed by both and fingerprinted before either writes against it; a divergence is a thaw (D22 W3).
- *Review rounds*: a fresh `spec-reviewer` each round with a generated context bundle (the unfolded
  statements, the Go functions, the call sites, the previous repair's diff). The cap on rounds is
  set by novelty, not by tier: four for a spec that follows a template or an existing one, more
  (raft-unified needed 11, and still missed 40%) for a new abstraction, stopping when a round finds
  no fix (only conformance); then the remaining findings are listed and the freeze goes ahead.
- *Call-order traces of callback interfaces*: for every interface the library calls back (a
  Storage, Ready/Advance, an apply callback), a trace of which methods Go calls, in what order, from
  which goroutine and in which state, recorded from the upstream tests and the driver, against which
  the interface's spec (its preconditions, its locking, its ownership) is checked before the freeze:
  Stage 2's trace validation for the interfaces between packages, where raft-unified's eight Go
  facts were.

Exit (the freeze): every caller's glue proves, the unfold list is empty, the probes are proved, the
rounds are done; the `Spec/` statements fingerprinted. After it, a spec change is a thaw.

### Stage 4: the trust frontier (tier M and L)

Every axiom and every non-allowed hypothesis the closed theorem reaches that is new in this run
(computed against the base commit) passes, before Stage 5:

1. *Consistency lint*: no axiom quantified over a semantics or instance parameter; a `False`-probe at
   the concrete instances.
2. *The spec-guided tester*: the axiom's pure pre and post evaluated over random call sequences of
   the real library, the predicates the specs hand out tracked, a frame check of the state the pre
   does not own, the library's upstream tests run against it (generalizing `etc/spec-test/bbolt`;
   generated from the Lean text, not transcribed).
3. *The `axiom` skill's refuter*: a Go program that panics while the axioms prove it does not. An
   axiom the tester cannot evaluate (stated with Iris resources only) fails this stage unless the
   refuter attacked it, and the report flags it "untested".
4. *Body first*: an axiom of a function whose Go source is translatable is a proof to write; no axiom
   of the package's own code.

A refuted axiom is restated (the weakest true statement its callers' glue accepts) and the glue
re-run; an `issues/` file whose code sits behind an axiom re-triggers that axiom's review (the gap
that let `Put_kv` stay false eleven days).

### Stage 5: prove, in parallel

Against frozen specs, one agent per function or small group, by file ownership, each with the brief
of `notes/proof-porting-task.md` made `briefs/prover.md`:

- the statement is fixed; touch only your files (a path filter on the diff, checked at merge); a
  private scratch directory; never `git add -A`; callees by their statements only;
- `etc/lean-check.py` for the loop; never `lake build` while others edit your imports;
- the proof patterns (`briefs/patterns.md`: worked proof files for each, from `main:notes/gotchas.md`,
  the perf rounds, CLAUDE.md "Proof writing"); `wp_auto` to the stuck point first;
- helpers: search the run's shared lemma module and the package's lemma files before proving one; a
  generic one goes to the shared module (`Proof/<pkg>/Lemmas/`), never a private copy;
- a body over about 400 lines is split into named local lemmas per branch or loop, proved with
  `--split`; budgets are per file, in tokens;
- commit every state that checks, the `sorry` narrowed (a death loses nothing unchecked); when
  stuck, narrow the `sorry` to the failing step, record the goal verbatim (any diagnosis marked as a
  guess), and report `blocked: <what>`;
- never weaken a statement, never delete a finished proof (a broken one keeps its text with the
  `sorry` on the failing step naming the commit that had it).

A proof is **done** only after `lake build` of its module (by the build owner) shows no "declaration
uses `sorry`" warning; `lean-check --fast` (no kernel) is never evidence. The fingerprint and TCB
delta run at merge.

### Stage 6: close

- Link; the closed theorems; `etc/tcb-report.py` delta against the base commit; `etc/api-check.py`;
  `etc/gen-interface.py --check --layout`; `etc/verified-code.py`; adequacy coverage; the clone
  detector (duplicated helpers merged).
- `proof-cleanup` and `proof-perf` passes, under the fingerprint.
- The final audit (above), then the report; `notes/STATUS.md` updated once, here; worktrees and the
  run's merged branches deleted; the branch committed and pushed.

## Autonomy: what replaces the human

**The adjudicator** decides a `blocked` report or a design fork. Its verdict needs a mechanical
witness, or it falls to the default:

| verdict | witness |
|---|---|
| the code is wrong | a Go test that fails on unmodified upstream, reached through the driver or the project's real callers, confirmed by a fresh refuter |
| the spec is wrong (a thaw) | a concrete state satisfying the pre where the goal is false, or a Lean refutation |
| a missing law | the law stated and proved in the owning package |
| a missing invariant | the invariant stated, and the failing proof step it discharges |
| a tactic problem | the default, when nothing else has a witness |

The panel (for design forks before the freeze only) is three differently prompted roles, one an
advocate for "this is the code's, or the axiom's, fault"; votes of one model are correlated, so
roles differ. Each decision goes to `notes/<run>/decisions.md`, marked "decided by the adjudicator",
for a human to read in a batch afterwards.

| decision (the user's so far) | gate |
|---|---|
| Scope | the driver fixes it: the code its execution reaches, in its configuration; the run cannot narrow the driver (hashed); scope narrowed inside proofs is listed (invariant 6) |
| The top-level statement | generated from the driver; never edited by the run |
| A design fork (options A/B) | each option drafted to statements by its own agent, the top two to glue; ranked by: no new axiom or hypothesis > fewer top-level premises > spec generality (no driver constant) > no new spec family > fewer changed `Spec/` files > smaller unfolded statements; the reviewer signs off |
| A new axiom | Stage 4; only for a function with no translatable body |
| A model assumption in Perennial | never: a local workaround, an entry in `notes/perennial-changes.md`, a proposed branch the run does not land |
| A fork fix to the Go code | the adjudicator's "code is wrong" witness; a fresh agent's triage against the nonissue criteria (`issues/README.md`: a precondition the real callers meet is a missing premise, not a fix; `AuthInfoFromTLS`); a capped diff; the upstream test suite and the mutation gate re-run on the fork; never a change for provability alone. The fork commit goes on a per-run branch of the fork, pushed (a standing permission the user grants once, at set-up; an unpushed pin fails `etc/goose.py --check`); never upstream |
| Changing a frozen spec (thaw) | the "spec is wrong" witness; at most two thaws per function, then its proof stays `sorry` with its report; a thaw re-runs review on the change and the glue of every caller |
| A spec family / mode split | forbidden (the lint); the only variant is a corollary of the one spec |
| Merge order across tracks | the scheduler: no two tracks edit one `Spec/` or `Inv*` file at once |
| Freshness / semantic strength | the strongest guarantee the Go documentation states; weaker only with a Go execution refuting the stronger |
| When to stop | the ledger (below) |

**Termination: the ledger** (`notes/<run>/state.json`, rebuilt from git on resume):

- review rounds per freeze as Stage 3 sets them; thaws at most two per function, counting only
  fixes and redesigns (below);
- every change to a frozen spec is classified as `notes/spec-first-plan.md` does (F fix, R
  redesign, W weakening, E extension, D decision, A adaptation, C conformance; found by proof, Go,
  test or check; public/trusted or internal), first by a classifier over the `interface/*.txt` diff
  (a statement changed in a caller only is A or C; a premise removed is W; a new export is E),
  then by an agent for what it cannot decide. Conformance, adaptations and extensions are not thaws:
  a cap on every edit would have stopped raft-unified's storage redesign and hundreds of harmless
  edits;
- a blocked task climbs a ladder: blocked once, a fresh prover with the goal; twice, the
  adjudicator; three times, the `sorry` stays with its report and the run moves on;
- the run stops when two prover waves in a row do not reduce the count of `sorry`s on the closed
  theorems' path, or at the token or wall-clock cap;
- **done** is: the gates pass, and that count is zero or frozen by the ledger, every remaining
  `sorry` named in the report.

## The orchestrator

A `Workflow` script (`.claude/workflows/autoverify.js`) over the run directory (`notes/<run>/`:
`state.json`, `inventory.md`, `decisions.md`, `report.md`). Resume is from git: each task is keyed by
its file, with the commit that set its status and its attempt count; the `sorry` list comes from
`etc/tcb-report.py`; tasks are idempotent and the orchestrator re-derives the queue on start (a
session can end at any point, not only at stage boundaries; after a death, the files it touched are
re-checked).

- **State on durable disk.** The run directory, scratch directories and resume state live under
  the repository or `/shared`, never `/tmp` (tmpfs, wiped at every restart).
- **Environment failures are not gate failures.** Every gate script exits with a distinct status
  when a tool is missing (`go` not on `PATH` makes `etc/goose.py` fail with `FileNotFoundError`,
  which reads as a failed `--check`), and the orchestrator checks the tools at start; the
  adjudicator never sees an environment failure as evidence.
- **Worktrees and branches.** The run's branch off `lean` at the frozen base; one worktree per
  parallel track; tracks merge into the run's branch within a day (none becomes a trunk); generated
  files regenerated after a merge, never hand-merged; notes are per-run files.
- **Builds.** One global build queue; one build owner per worktree; provers use `lean-check` only;
  builds at gates target the closed theorems' roots; a full build at Stage 6 and nightly; the
  prover count capped by the memory budget; a flaky failure retried once, then treated as a tactic
  race; a module over the time or memory ceiling goes to the `proof-perf` patterns before it lands.
- **Roles** (each a brief in `.claude/skills/autoverify/briefs/`): designer, spec author (the `spec`
  skill), reviewer (`spec-reviewer`), axiom tester, axiom refuter (the `axiom` skill), model-strictness
  tester, prover, adjudicator, auditor (the final audit), perf, cleanup. A reviewer, refuter, tester
  or auditor never sees the author's reasoning.

## The report

`notes/<run>/report.md`, generated, and the branch's last commit. First line: "verified code =
<project> @<rev> + an N-line diff (k fixes)". Then:

1. The closed theorems, stated as what they are (partial correctness), with their drivers (path,
   lines), the configuration bounds, the Go model each checks against, the mutation score and the
   classified survivors (hangs among them).
2. The trusted surface's delta against the base commit: new axioms and hypotheses (each with its
   tester runs, refutation attempt, upstream tests), trusted models and Goose configuration changes,
   environment models with their deviations, porcupine's soundness if (b) is not proved, the codec
   if unverified.
3. Scope: the configuration diff; scope narrowed inside proofs (invariant 6).
4. `sorry`s left, each with its `blocked` report and ladder history.
5. Coverage: functions verified, reached by a theorem, unreached; `etc/verified-code.py`.
6. Findings: `issues/` files (Go bugs with reproductions, after nonissue triage), fork fixes, spec
   bugs (`notes/`).
7. Decisions taken by the adjudicator; thaws with their witnesses.
8. Costs: wall time, tokens, build time per stage; spec changes after the freeze, classified, with
   the metric (fixes and redesigns, by how found, against the size of the frozen spec). The run
   writes its own costs to `notes/<run>/costs.json` as it goes: tokens and agent time are
   otherwise only in session transcripts, which Claude Code deletes after 30 days
   (`/shared/transcripts-archive` keeps copies).

## What to build

**First, the minimal version** (tier S, enough for the logkv replay):

1. `.claude/skills/autoverify/SKILL.md` for tier S (Stages 0, 3 with one review round, 5, 6),
   `briefs/prover.md`, `briefs/patterns.md`, the ledger in `state.json`, one session (no Workflow
   script), its resume tested by killing the session once mid-proof.
2. Derived link lists, and stubs with callee hypotheses (the only generators logkv needs).
3. The checks: the prover's diff within its files; no "declaration uses `sorry`" after `lake build`;
   the binder check; the bypass lint; the immutable set compared with the base commit.
4. Driver gate 1 (green under stress, `-race`).

**Then, as tier-M and L targets need them**: the remaining driver gates (mutation testing with
hang-aware killing, model strictness, the early-return and exact-`Ok` lints, coverage, the
constant-leak lint); Stage 4's generated tester; the inventory generator (from `etc/k8s-worklist.py`);
the context bundle; the Workflow orchestrator, build queue and memory budget; the final audit job;
the executable `Step` with trace replay, then the PSM library. Off the critical path, as research:
porcupine's soundness, or deliverable (b) through `LinTheory`, which makes it unnecessary.

**First use of the binder check**: replace `rnStopOkStarted` (the server theorems' vacuous premise)
by a proof or a gated axiom.

## Testing the skill

1. **Blind replay, uncontaminated**: the logkv family, with every logkv reference stripped from the
   skill (its briefs and templates may use `counter`, the template the 112-minute baseline had), so
   the comparison is not against a skill trained on its answer; and a held-out new program of the
   same size, written for the test. Then `pkg/wait` or `idutil`, the btree, the cache. Compare with
   the history: time, spec revisions after the freeze, `sorry`s, axioms, bugs.
2. **Re-verification**: raft's proof at a new upstream revision (the commits after `b867cf13` on
   etcd-io/raft's `main`), from the current proofs. The witness experiment (three days by hand, 16
   defects of etcd-io/raft#168) is the baseline for a variant.
3. **A new distributed package**: the first run of Stage 2 without a human, on a protocol whose
   messages carry monotone knowledge (a lease protocol needs a time model first): a Paxos-like
   register, or raft refactored onto the PSM library and re-proved.
4. **The gates, one by one: a spec-mutation benchmark.** Plant defects in frozen specs (a premise
   dropped, a postcondition strengthened past the code, an ownership swapped, a call-order fact
   reversed; drawn from the classified history) and record which gate catches each (review, glue,
   tester, probe, call-order trace, proof) and at what cost. The replays measure the result; this
   measures each gate, and whether a cheaper gate could stand in for a dearer one.
5. **The algorithm itself: an ablation.** The same target (a held-out tier-M package) run
   spec-first and code-first (each function proved bottom-up, specs revised as callers need), by
   the same agents and budget: spec changes, rework (proof lines deleted), time to the closed
   theorem, bugs found.
6. **The human's part, measured.** Every decision the user took in the stages so far is classified
   as *intent* (the top-level statement, what may be trusted: the driver, an axiom) or *judgment*
   (a design fork, a merge order, a fix); the claim is that only intent needs a human. A ready data
   point: seven trusted changes of raft-unified's repair (Stage P's P2, P4, P5, P6, P8, P9, P10) were
   approved by the coordinating agent while the user was away; the user's review of them is a
   measurement of how often a human reverses such a decision.
7. **Measured**: zero human interventions during the run; spec revisions after the freeze; refuted
   axioms that reached Stage 5 (should be none); mutation scores; the costs; and, afterwards, whether
   a human reading the report reverses an adjudicated decision or reclassifies a fork fix as a
   nonissue (each becomes a sharper gate).

## Risks

- **The trusted surface without a human.** The largest. The invariants and the final audit keep the
  run from changing it silently; the gates on axioms (tester, refuter, body first) target the
  history's false axioms, 31 of 44 of which have a refuting Go execution; the 13 unobservable ones
  (framed-out writes, proposals without a permit) are why the frame check and the refuter exist. The
  report lists the surface's delta first.
- **A weak theorem.** Partial correctness, a weak driver, a permissive model: the hang-aware mutation
  gate, the model-strictness tests, the exact-`Ok` lint and coverage bound it; the report states it.
- **Adjudicated forks and fork fixes.** Witnesses make verdicts checkable; the nonissue triage and
  the diff cap bound fork fixes; the batch review afterwards corrects the rest.
- **Cost.** Tiers and caps bound it; the report makes it visible.
- **Perennial gaps.** A run cannot change Perennial; gaps are counted at Stage 0 and abort the run
  early when they block the driver's path.

## Reviews (2026-10-30)

Four fresh reviewers read the first version, each given the plan and the repository, not the
author's reasoning. What each changed:

- **Soundness**: the trusted surface and the run's invariants (typeclass hypotheses, trusted models
  and the Goose configuration, gate scripts and baselines the run could rewrite, Lean bypasses, the
  hand-written program term); hang-aware mutation; fixed thresholds; model strictness; the exact-`Ok`
  lint; the driver hashed; fork fixes reproduced on upstream with a capped diff; untestable axioms;
  corrected claims (the closed theorem is hand-written today; stubs check no precondition; the tester
  ran only on bbolt; `CheckQuorum`/`PreVote` are etcd's setting, not raft's default).
- **Feasibility**: the ledger and the definition of done; Stage 2's exit relaxed (statements
  reviewed and admitted, proofs a Stage 5 track); verdicts with witnesses; prover gates that do not
  need a full build; the build queue and memory budget; per-run registrations instead of shared
  tables; an early abort on a Perennial gap; long proofs split; resume from git; tiers; the
  contaminated replay; the minimal version.
- **History**: fork fixes that passed their test but were nonissues; scope narrowed inside proofs
  (D19m-p); callee-free stubs hiding axioms; every `--update` self-certifying; environment models'
  failure semantics (D50/D51); placeholder axioms drifting (W3); duplicated helpers; Perennial pins
  moving; the Rocq journal's process failures; worked examples over prose; testing `sorry`'d specs;
  housekeeping; the existing inventory, gate and deep-ownership scripts; D51's choice stated
  correctly; seeds versus runs under stress.
- **Methodology**: partial correctness stated; the three deliverables (driver theorem for every
  configuration, the library-level linearizability theorem, the API specs); `MainWith(cfg)` and the
  constant-leak lint; an executable `Step` with trace validation against Go and model checking over
  the same `Step`; the PSM pattern's limits (FIFO, time) and a library proved on a second protocol;
  a verified fault-drawing transport and the codec; simulated crash-restart drivers; error meanings.
