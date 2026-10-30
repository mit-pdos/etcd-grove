# Plan: a skill for autonomous, end-to-end verification of a Go package

Status: proposed (2026-10-30, branch `worktree-autoverify-plan`). Nothing built yet. Written from
the history of this repository (3.4k commits on `lean` since 2026-10-06, the Rocq development on
`main`), read through five themes: the protocol layer, proof engineering, the trust base, the
test drivers and concurrency, process and orchestration. Supersedes nothing; it builds on
`notes/spec-first-plan.md` (whose steps it automates) and the `spec`, `axiom`,
`progressive-verification`, `proof-perf` and `proof-cleanup` skills (which it calls).

## Goal

Given a Go package (or a few that form a system: raft; a server over raft) and a Go test of it, run
**without a human in the loop** to a closed theorem: *every real execution of the test's program
ends with no thread stuck and none panicked*, linked through proofs of the package's code, with a
trust base that is reported, tested and adversarially reviewed. The human's part is to audit at the
end, if they want: the Go test (the top-level spec), the list of premises and axioms the theorem
rests on, and the `issues/` found. Nothing during the run waits for them.

Two user decisions (2026-10-30) fix the shape:

1. **The top-level spec is the adequacy theorem of a Go test.** The trusted statement is Go code
   that anyone can read and run (`examples/kv`'s `Main` with porcupine's check), plus Perennial's
   adequacy theorem; no Lean statement of the package's behavior has to be audited. Every closed
   theorem the repository has is already of this form (`notes/STATUS.md`, "The closed theorems").
2. **Autonomous.** Every decision the user took during the stages so far (eight in M2's first day;
   scope, design options, axioms, fork fixes, merge order: `notes/spec-first-plan.md`, "Who
   decides") becomes a gate: a mechanical check, a fixed rule, or an adjudication by fresh agents
   against fixed criteria. The rules that kept the work sound under a human (no statement weakened,
   no family of specs, the trust base not growing silently) become hard checks, because nobody will
   catch their breach by reading.

**Push-button** means: the input is a pinned Go revision and a test; the output is a branch with the
theorem, its report, and the issues. A run may stop short (a `sorry` left, an axiom refuted and not
yet replaced, a Go bug that needs a fork fix), and then it says exactly where, as the proofs here
always have.

## What the history says (the evidence the plan rests on)

Each point is a rule below; the sources have the details.

**Specs.**
- Spec churn is the main cost, and it is not falsity: of 64 sampled revisions of existing specs, 23
  were a caller needing more and 20 a scope widening; 3 were false behavior
  (`notes/spec-first-plan.md`, step 1). `raft__Step` was revised 48 times, almost all widenings
  (message types, learners, joint configurations, PreVote, CheckQuorum, snapshots, transfer).
  So: fix the scope first (the test does), draft every spec top-down, prove the glue before the
  bodies.
- Reviews before proofs find most spec problems (the compactor: 18 of 19 first-tier revisions came
  from fresh-reviewer rounds; the 19th from glue), and repairs introduce defects (a round after
  every repair). The freeze leaked once, through a caller that did not exist yet: freeze only when
  every caller's glue proves.
- Mode families are the most expensive mistake: auth's on/off copies, about 7k lines, every other
  track editing both copies (`notes/auth-mode-merge-plan.md`). One spec per function; a mode is
  state.

**The protocol layer** (raft; `Proof/go_etcd_io/raft/v3/Protocol/`, 21k lines).
- What worked is a *permissioned state machine* in three layers: Go heap ↔ physical node state
  (`ownRaftPhys`), physical ↔ protocol state (a pure relation), protocol state ↔ ghost knowledge
  (`ownRaftGhost`). A per-node `Step` relation of plain values whose rules mirror the Go transitions,
  reflexive and transitive (one Go function that takes several steps refines one `Step`), the outbox
  in the state with a drain rule. Node-local ghost authority; everything a step learns is persistent
  knowledge carried on the message (`isMessage` by cases on the message type), so delay,
  duplication and reordering cost nothing; election safety is the agreement of two persistent facts.
  One ghost update (`ownRaftGhost_step`) at one dispatcher (`raft.Step`'s `finish_branch`); every
  spec below it is a physical triple with a pure `Step` witness. That made widenings mechanical
  (B7: about 40 branch files, 8000 lines, converted by recipe in a day).
- The one global invariant (`raftCommitInv`: committed log, winners) was forced, found by stating
  the safety theorems early as admitted lemmas: two nodes' local state could not prove them.
- For a hard widening (reconfiguration), paper proof → adversarial review against the Go code →
  small explicit-state model checker with planted bugs → Lean model and invariants rule by rule →
  ghost at the old scope → general case → code. B5 was proved the same day, "no false paper
  statement". The checker found no new bug but validated fixes and gave minimal traces; the review
  found the read-index bugs fixed upstream (raft#535, #536).
- Widening is cheap behind a single hook (`CfgAt`: one lemma, three uses) and expensive when
  messages lack fields (`Msg` had only `voters`; snapshots, D22: 188 commits) or knowledge belongs
  to the application (snapshot contents).
- False statements at this layer were claims about Go never checked against it (term wrap, `None
  = 0`, the empty voter set's majority, `AppOk`'s commit index): nine of ten in main's table.

**Proof engineering.**
- Effort split (Rocq, `main:notes/proof-effort.md`): tactic trial and error about 50%, reading
  generated code 20%, ownership plumbing 20%, the protocol argument 10%. Agents are good at the
  last three when the first is cheap: the incremental checker (`etc/lean-check.py`, 2026-10-26,
  three weeks in) is the biggest lever and must exist from day one.
- The per-function spec/proof/link discipline made parallel proving and the retarget work: the whole
  Rocq raft proof was ported in about three days by parallel agents over fixed statements.
- Performance is a property of proof patterns, fixable once: targeted dispatch instead of trying
  every spec (`raft__Step/Dispatch.lean`: 5223 s → 1250 s CPU), `wp_join` instead of re-verifying
  the tail per branch (911 s → 63 s), loops given only what they read, framing by name. Flakiness
  came from global state in tactics; silent admits from `wp_apply … $$ [frames]` (only the
  "declaration uses `sorry`" warning shows them).
- Re-verification (raft v3.7, 139 functions changed): the pure model survived as a rename; the
  physical predicates (messages, entries, snapshots) took the bulk (R4/R5, about 32k lines). A
  parallel tree kept the trunk green until one mechanical swap.

**The trust base.**
- 766 axioms today; 47 known to have been false, mostly found by reading after proofs rested on
  them (`notes/audit.md`; one stayed false 9 days, one 11). Three were inconsistent in Lean
  (quantified over a semantics instance). 31 of 44 had a refuting Go execution; the spec-guided
  tester (`etc/spec-test/bbolt`, about 25 lines of Go per axiom) refuted every false bbolt row with
  no false alarm in 10 000 runs; the `axiom` skill refuted two more with a sorry-free Lean proof
  next to a panicking Go program (`examples/axiomcx`).
- Top-level premises went wrong in three ways: vacuous (`isLogger` held of no logger, found only
  when a closed driver was built; `server_new_auth_on` contradicted `kvInv`), unsatisfiable at the
  deployed size (a per-member registry for three members), excluding the deployed configuration
  (CheckQuorum off while etcd runs it on; one member; monitors off).

**The drivers** (`examples/`, the closed theorems of `notes/STATUS.md`).
- Two tiers. The clean one (`lintest`'s counter and logkv family, `kv_porcupine_safe`,
  `kv_witness_porcupine_safe`) takes no Iris premise: about 100 lines of Go and a 15-line theorem
  to audit, 53 axioms (Go's semantics and Lean's three). The server tier (`putget_safe` through
  `k8setcd3_safe`) takes `premises`, a conjunction of assumed Hoare triples, and those were false
  twice: `∀ n, rnStopOk n` (D19r) and its replacement `rnStopOkStarted`, still open
  (`notes/raft-spec-review.md`, "High 1"; `notes/STATUS.md`), which makes every server theorem
  vacuous today. An assumed triple at the top is a trusted statement in separation logic, the
  opposite of an auditable test.
- Building a closed driver is the vacuity check that worked (raft's `isLogger`, the workload
  clause a delete-then-put transaction refutes, D19c; the feature-gate contract), but only for pure
  premises.
- The drivers are weaker than they look: every etcd driver returns without checking on an error
  (`putget`'s `if err != nil { return }`), so a server that always fails passes them; `k8setcd3`
  skips porcupine after a failed write. The kv cluster's transport drops message types raft's spec
  does not cover. The DaemonSet `Main` is false of its code (D51: `TestMainNeverPanics` fails 2 runs
  in 100), found by running it.
- "Never panics" with porcupine is linearizability of the histories the driver generates, *given
  porcupine's soundness*: its proved spec is completeness only (`Linearizable → r ≠ "Illegal"`,
  `Spec/github_com/anishathalye/porcupine/CheckOperationsVerbose.lean`); that `Ok` implies
  linearizable is trusted, with the Go model.
- Calibration (`notes/logkv-eval-summary.md`): a fresh agent proved an 84-line concurrent program
  end to end in about 112 minutes (344 spec lines, 1316 proof lines); each one-feature variant in 8
  to 19 minutes.
- Not covered by any driver theorem: crashes (no proof of `durablekv`), liveness, a real network
  (the network is the `Transport.Start` axiom in one process; no distributed adequacy in the Lean
  port, D21a).

**Bugs found.** About 30 by writing specs, about 30 by proof attempts, about 18 by designing a stage
(listing what a function writes), about 9 by adversarial review (the highest value per finding),
few by running things, none new by model checking. Spec-writing is a bug finder in its own right
and runs first.

**Process.** Bottom-up units gated after each (build, TCB per collection, verified-code count);
contract-first axioms at the frontier replaced later without changing callers; an inventory before a
redesign; static case first, dynamic as an extension with the old statements as corollaries;
temporary premises named and grep-able. Failures: a stage branch that became the trunk, specs
proved before anyone checked they were satisfiable, long sub-stage chains each adding a variant.
Agents drift to proving and delete finished proofs (M2's S1 agent re-proved about 45 files).

## The top-level spec: a Go test

The run's statement is fixed before anything else, and it is Go.

**The driver.** A `Main` (in `examples/<name>/`, its own Go module) that builds the system as
deployed (configuration from the project's defaults: etcd's `CheckQuorum` and `PreVote` on, three
members), runs a randomized workload from a seed it draws itself (so the theorem covers every seed),
and checks the outcome in Go, panicking on a violation:

- *linearizability*: a history recorded by the clients, checked by porcupine against a sequential
  model written in Go (`examples/lintest`, the kv family, `k8setcd3`); the model is part of the
  audited spec, so it is small and obviously right;
- *safety invariants*: assertions on observed state (watch events exactly the writes, `watchkv`;
  at most one pod per node, the DaemonSet controller);
- *environment*: faults the system must tolerate are the driver's choice too (`linkv3p` cuts and
  mends links on a schedule it draws, so the theorem holds for every schedule).

The closed theorem, generated (`Adequacy.lean`/`Results.lean` as in `examples/kv`): for every real
execution of `n < 2^63` steps from a fresh state with one thread, no thread stuck, none panicked,
the main thread's result as stated; `#print axioms`.

**What makes a driver a good spec** (checked mechanically, as gates, before any proof):

1. *It runs green in Go*: the driver run as a Go test over many seeds (at least 100), with `-race`.
   A driver that fails in Go is a Go bug (`issues/`, the failing seed as reproduction) or a wrong
   model; the run does not prove a program Go refutes (D51).
2. *It never gives up silently*: no early return on an error. A failed or timed-out operation is
   recorded as an indeterminate output that porcupine checks (`linkvtxn`'s `Output.Err`), not
   skipped; a lint over the driver flags every `return` on an error path. The count of checks
   actually reached per run is measured: a check that most runs skip is reported.
3. *It catches mutants*: Go mutation testing of the package (flip a comparison, drop a persist,
   skip a quorum check, reorder an unlock, always return an error, always return the initial
   value) must make the driver panic on some seed for a set share of the mutants; the survivors are
   listed in the report as what the theorem does not say. A driver that a trivial implementation
   passes says nothing.
4. *It reaches the code*: adequacy coverage (the `Link.lean` theorems a closed theorem reaches,
   measured in `notes/STATUS.md`, 2026-10-21) must be every function the run claims verified. A
   function proved but unreached is reported as unaudited (the client's `concurrency`: 0/107).
5. *It is the deployed configuration*: a diff of the driver's configuration against the project's
   defaults is part of the report; every difference is a scope restriction, listed. A filtering
   transport (the kv cluster's `deliverable`) or a bound kept only for the proof (`ticks`) is one.
6. *Its premises are pure*: the theorem's hypotheses are only the step bound (overflows paid by
   time receipts, D19b), the package's semantic assumptions, `IsInit`, and named pure environment
   premises, each with a satisfiability witness instantiated at the driver's concrete values in
   Lean. **No Iris premise at the top** (stricter than D19a, which allowed triples whose post holds
   only fresh resources: that is how `rnStopOkStarted` got in). What the proof needs of an
   unverified callee is an axiom, where Stage 4's gates apply.
7. *Its checker is sound*: with porcupine, the statement is only as strong as "`Ok` implies
   linearizable". Either porcupine's soundness is proved once (its translation is already verified
   for completeness), or the theorem also exports `Linearizable` of the recorded history through a
   ghost or pure statement. Until one is done, the report names porcupine's soundness and the Go
   model as trusted.

The driver is Goose-translatable Go, which shapes it (flat input and output structs, not slices, so
the model decodes purely; `linkvtxn`). Proof artifacts inside it (prophecy resolution) are marked and
kept out of the checks. A good template is `examples/lintest` (`Run(model, apply, gen, clock,
clients, ops)`: concurrent clients record porcupine operations, the real checker runs, `Main`
panics unless `Ok`), whose `applySpec` makes any logically atomic library a porcupine example.

Several drivers per system are fine (a kv workload, a partition schedule, a watch); each is a
theorem. Upstream tests are sources, not drivers: raft's `datadriven` tests need file I/O, `fmt`
and golden files, and as a spec say only "the output equals a transcript"; etcd's robustness tests
fit better (porcupine models, traffic weights), rewritten into translatable Go as `linkvtxn` did,
with a differential test of the rewritten model against the upstream one. A run that is given no
test writes one from the package's documentation and its upstream tests; that driver passes the same
gates, and the report flags it as written by the run.

**Out of reach today**, so not claimed by any run until Perennial supports it: crashes and
recovery, liveness, a network outside one process. A driver for a distributed system runs its nodes
in one process over a transport whose contract is an axiom (lossy, duplicating, reordering), and the
report says so.

## The pipeline

Each stage has an entry condition, its work, and an exit gate that is mechanical. Stages run in
this order per system; within a stage, work fans out to agents over fixed statements.

### Stage 0: set-up (once per project)

- A Goose project in `etc/goose.py` (pinned revision, `GO_TOOLCHAIN`, `-lean-root`), its
  configuration `Code/**/*.toml`, the translation, `--check` in CI.
- The layout, modules, package API lists (`etc/api/<pkg>.txt`), generated initializers
  (`etc/gen-init.py`), generated links with **callee lists derived from the `wp_proof` hypotheses**
  (new: today 36 hand-written `etc/link-lean-first*.txt`), a TCB collection, the statement
  fingerprint (`.claude/skills/proof-perf/fingerprint.py`) of the roots, `etc/timed-build.py`.
- Exit: the translation builds; `wp_auto` runs each function to its end or to its first stuck point
  (the *stuck-code smoke test*, new: a translated body with no semantics step, `IndexRef` on an
  array value, is found before anyone designs an invariant for it); a translator gap is recorded in
  `notes/perennial-changes.md` and worked around locally (CLAUDE.md, "Changes to Perennial").

### Stage 1: inventory

- The call graph from the drivers down; each function classified: pure, sequential with heap,
  lock-protected, channel/goroutine, protocol step (touches state another node reads through a
  message), trust frontier (an untranslated callee).
- For a re-verification (a new revision of verified code): the function-level diff against the
  proved revision, each proof file classified as the retarget's R0 did (pure / Go values / shared
  predicates / names changed types), and the cheapest path measured before the plan is fixed.
- Exit: the inventory file (`notes/<run>/inventory.md`, generated) and the stage list below with
  the functions of each.

### Stage 2: design (distributed packages: the permissioned state machine)

For a package whose correctness is a protocol across nodes (raft, a lease protocol, a replicated
store), before any spec:

1. *The model*: `PState` (plain values), `Step id s recv s'` with one rule per Go transition, written
   while reading the generated body; reflexive and transitive; outbox in the state, drain rule;
   messages with every field the Go message has. Each varying parameter (the configuration) behind
   one predicate with one lemma.
2. *The safety theorems* stated over the model as admitted lemmas, with the invariant they need, and
   a paper proof in the notes.
3. *Adversarial review* of the model and paper proof against the Go code, by a fresh agent told to
   find a Go execution that breaks a rule or a lemma (the reconfiguration review is the template).
4. *A small explicit-state checker* of the model (Go, as `issues/raft-conf-lag-model/`), with
   planted bugs that it must find (a checker that finds no planted bug is vacuous).
5. *The ghost design*: node-local authority, persistent knowledge, `isMessage` by message type, a
   global invariant only where step 2 showed local state cannot prove the theorem; the allocation
   lemma (`ownRaftGhost_alloc`) at once, so no predicate is vacuous; the one ghost update lemma.
6. Then the Lean proofs of the invariants rule by rule (they find model errors: `AppCommitEq`).

Exit: the model, ghost and safety lemmas proved (no `sorry` at this layer: it is small, about 10%
of the effort, and everything above rests on it), the checker's report, the review's report with
every finding resolved.

For a concurrent (not distributed) package, the design is the lock invariants and the
linearization points: an atomic update in the triple (TaDa style: the library's specs take and give
back ghost state the client owns; no caller-supplied predicate as a parameter), thread tokens for
goroutines, persistent contracts for concurrent callers, tokens for once-only resources
(`.claude/skills/spec/PRINCIPLES.md`, "resources"). The designs that recurred become templates
(`briefs/concurrency.md`), each pointing to its first use:

- *helping through the lock invariant*: the writer leaves its atomic update in a pending slot, the
  applier fires it at the linearization point, the result returns through a saved proposition keyed
  by a mono-list index; slots split done/pending at `applied` (`examples/lintest/logkv`, the kv
  store, the server's request path);
- *one-shot handoff*: a buffered(1) channel with at most one send then close, two half-owned ghost
  variables (`cache/v3/Handoff.lean`, reused by `pkg/v3/wait`);
- *`Once` with a lent resource* (`OnceFrame`), *broadcast epochs* (a mono-nat epoch and
  close-to-broadcast channels, `InvNotifier`), *producer/consumer halves* (`InvWatcher`), *slots
  beside an RWMutex* (`InvDemux`);
- *thread tokens* for every goroutine and wait group (Perennial's `threadTok`; `Add(n)` as a local
  lemma), *time receipts* for every counter that could overflow;
- each part of an invariant a named predicate with read and update lemmas, never destructured by
  position in every proof (half of logkvsnap's changed lines were that).

### Stage 3: the spec skeleton, top-down

From the driver down, every function's spec in its `Spec/` file, every proof `sorry` or an
axiom at the trust frontier, `Link.lean` generated, the closed theorem stated and building over the
`sorry`s (it is the satisfiability check of every precondition on the path: the vacuous `isLogger`
would have shown here). The `spec` skill writes each spec; its hard rules are checks:

- *one spec per function*: a lint over `Spec/` rejecting a second triple of a function or a
  suffixed predicate family beside an unsuffixed one (`specOn`, `…C`) (new);
- *local*: the spec's footprint, not an aggregate;
- *no cross-package unfold*: a lint over the glue proofs (every `unfold`/`iunfold`/positional
  destructuring of another package's definition) (new; today counted by hand); each is a missing
  law, added to the owning package;
- *complete*: every caller's glue proved (the glue: callers whose bodies only thread state). Glue is
  full separation logic: most caller needs were resources (a fraction lent, a token threaded).

Then the review rounds (`spec-reviewer`, fresh each round, given a generated context bundle: the
unfolded statements, the Go functions, the call sites, the previous repair's diff) until a round
finds nothing in the first tier. Then the probe: one easy and one hard body per package, proved.

Exit (the freeze): every caller's glue proves; the unfold list is empty; the last review round is
clean; the probes are proved; the fingerprint of every `Spec/` statement is recorded. After the
freeze, a spec change is a *thaw* (below), never a silent edit.

### Stage 4: the trust frontier

Every axiom the closed theorem reaches that is new in this run passes, before Stage 5:

1. *Consistency lint*: no axiom quantified over a semantics or instance parameter (the three
   inconsistent ones); `#print axioms` of a `False`-probe at the concrete instances.
2. *The spec-guided tester*: the axiom's pure pre and post (in the canonical form,
   `notes/spec-first-plan.md`, Test) evaluated over random call sequences of the real library, the
   predicates the specs hand out tracked (`etc/spec-test/bbolt`, generalized and generated from the
   Lean text instead of transcribed: new), with a frame check of the state the pre does not own, and
   the library's own upstream tests run against it.
3. *The `axiom` skill*: a fresh agent tries to write a Go program that panics while the axioms prove
   it does not; a refutation is a Lean proof plus the Go program (`examples/axiomcx`).
4. *Read the callee's body first*: 6 of 19 axioms of one round were of no-op functions; an axiom of
   a function whose Go body is translatable is a proof to write, not an axiom.

A refuted axiom is restated (the weakest true statement its callers' glue accepts) and its callers'
glue re-run; any `issues/` file whose code sits behind an axiom re-triggers that axiom's review
(the gap that let `Put_kv` stay false eleven days).

### Stage 5: prove, in parallel

Against frozen specs, one agent per function or per small group, assigned by file ownership (no two
agents on one file), each with the brief of `notes/proof-porting-task.md` made the skill's
`briefs/prover.md`:

- the statement is fixed; touch only your files; callees by their statements only;
- `etc/lean-check.py` for the loop (`--goal`, `--fast`, `--split` for long proofs); never `lake
  build` while others edit your imports;
- the proof patterns (`briefs/patterns.md`, from `main:notes/gotchas.md`, the perf rounds, CLAUDE.md
  "Proof writing"): records as variables, `word`, `wp_join` after a case split, loops given only
  what they read, framing by name, dispatch by the next redex, `wp_auto` to the stuck point first;
- a budget (about an hour per lemma, as the port's); when stuck, narrow the `sorry` to the failing
  step, record the goal verbatim (any diagnosis marked as a guess), and report `blocked: <what>`;
- never weaken a statement, never delete a finished proof (a broken one keeps its text with the
  `sorry` on the failing step naming the commit that had it).

Each finished proof: no "declaration uses `sorry`" warning (the silent admits), the fingerprint of
the frozen specs unchanged, its module under the time and memory ceilings (a module over them goes to
the `proof-perf` patterns before it lands).

A `blocked` report goes to the adjudicator (below), which decides among: the spec is wrong (a thaw),
the code is wrong (a Go bug: `issues/`, a reproduction), a missing law (added to the owning package),
a missing invariant (back to Stage 2 or the package's `Inv*`), or a tactic problem (a fresh prover
with the goal).

### Stage 6: close

- Link, the closed theorem without `sorry` on its path (or with each remaining one named),
  `etc/tcb-report.py --check` and the collection, `etc/api-check.py`, `etc/gen-interface.py --check
  --layout`, `etc/verified-code.py`, adequacy coverage.
- `proof-cleanup` (dead declarations) and `proof-perf` passes, both under the fingerprint.
- The report (below).

## Autonomy: what replaces the human

Every decision point of the history, and its gate. The adjudicator is a fresh agent (or a panel of
three, majority) given the options, the criteria and the evidence, never the author's conclusion;
its decision and reasons go into `notes/<run>/decisions.md`, marked "decided by the adjudicator", so
a human can read and reverse them in a batch later (before the freeze a reversal costs statements,
not proofs).

| decision (the user's so far) | gate |
|---|---|
| Scope: what a stage verifies | the driver fixes it: the code its execution reaches, in its configuration. The run cannot narrow the driver; it can only report what it left `sorry` |
| The top-level statement | generated from the driver; never edited by the run |
| A design fork ("stopped for a decision", options A/B) | each option drafted by its own agent to statements and glue; ranked by: no new axiom > fewer top-level premises > no new spec family > fewer changed `Spec/` files > smaller unfolded statements; the reviewer signs off on the winner |
| A new axiom | Stage 4's four gates; and only for a function with no translatable body (names-only, or a library outside the run). An axiom of the package's own code is not allowed |
| A model assumption in Perennial | never (CLAUDE.md, "Changes to Perennial"): a local workaround, an entry in `notes/perennial-changes.md`, a proposed branch off Perennial's `lean` that the run does not land |
| A fork fix to the Go code | only with a Go test that fails before and passes after, the project's own tests green, the driver green; the run fixes its fork, records the issue in `issues/`, and never pushes upstream |
| Changing a frozen spec (thaw) | the adjudicator, given the blocked report; the thaw records its cause (the spec-first rubric) and re-runs review on the change and the glue of every caller, then the proofs whose fingerprint changed |
| A spec family / mode split | forbidden (the lint); the only variant is a corollary of the one spec (`spec_R : spec → specR`) |
| Merge order across tracks | the scheduler: two tracks never edit the same `Spec/` or `Inv*` file at once |
| Freshness / semantic strength choices | the strongest guarantee the Go documentation states; weaker only with a Go execution refuting the stronger |
| When to stop | budgets (below) |

What still goes to a human, after the run: nothing blocks on them. The report puts first the items a
human would most want to see: the driver and its model, the top-level premises, the new axioms with
their tester and refutation results, every thaw, every adjudicated fork, every fork fix of the Go
code, every `issues/` file.

## The orchestrator

A `Workflow` script (`.claude/workflows/autoverify.js`) and a run directory
(`notes/<run>/`: `state.json`, `inventory.md`, `decisions.md`, `report.md`), resumable from
`state.json` at any stage boundary (a run is days; sessions end).

- **Worktrees and branches.** The run's branch off `lean`; one worktree per parallel track; tracks
  merge into the run's branch within a day (none becomes a trunk); generated files (`Link.lean`,
  `Init.lean`, interfaces, the TCB baseline) are regenerated after a merge, never hand-merged; notes
  are per-run files, never one shared line (the "Last updated" conflict magnet).
- **Builds.** One build owner per worktree; provers use `lean-check` only; a full build at each
  stage gate and before a merge; peak memory per module watched (a 17 GB compile was not
  committable); a flaky failure is retried once and then treated as a tactic race (no global state
  in tactics).
- **Roles** (each a brief in `.claude/skills/autoverify/briefs/`): designer (Stage 2), spec author
  (the `spec` skill), reviewer (`.claude/agents/spec-reviewer.md`), axiom tester, axiom refuter
  (the `axiom` skill), prover, adjudicator, perf, cleanup. A reviewer or refuter never sees the
  author's reasoning.
- **Budgets.** Per lemma about an hour; per review round about 15 minutes; per stage a wall-clock
  and token budget from the inventory's size; a stage over budget narrows to the next gate and
  reports. The run's report says what each stage cost.

## The report

`notes/<run>/report.md`, generated, and the branch's last commit:

1. The closed theorems, with their drivers (path, lines), the Go model each checks against, and the
   mutation score (with the surviving mutants).
2. The premises of each theorem, by kind, with their satisfiability witnesses; the configuration
   diff against the project's defaults.
3. The trust base: axioms reached (new ones first), each with its tester runs, its refutation
   attempt, the upstream tests run; `sorry`s left, each with its `blocked` report.
4. Coverage: functions verified, reached by a theorem, unreached; `etc/verified-code.py`.
5. Findings: `issues/` files (Go bugs with reproductions), fork fixes, spec bugs (`notes/`).
6. Decisions taken by the adjudicator; thaws with their causes.
7. Costs: wall time, agent tokens, build time per stage; spec revisions after the freeze (the
   spec-first metric).

## What to build

In order; each is useful on its own to the current manual process.

1. **The skill files**: `.claude/skills/autoverify/SKILL.md` (the pipeline above, as rules),
   `briefs/*.md` (one per role, from the task notes that worked: `proof-porting-task.md`,
   `protocol-proof-task.md`, the spec-first agents' brief), `briefs/patterns.md` (the proof
   patterns), `LESSONS.md` (each run's misses, as the other skills' are).
2. **Derived link lists** (`etc/gen-link.py` generic, reading the `wp_proof` hypotheses).
3. **The lints**: one spec per function / no families; cross-package unfolds; silent admits (every
   new proof's `sorry` warnings); top-level premise kinds; axioms quantified over instances.
4. **The driver gates**: `go test` over seeds with `-race`; the early-return lint and the
   reached-check count; Go mutation testing of the package against the driver; the
   adequacy-coverage script (today a one-off measurement); the configuration diff; the
   no-Iris-premise check on closed theorems. And once, for every porcupine driver: porcupine's
   soundness (`Ok` implies linearizable) proved, or the theorems restated to export `Linearizable`.
   First use: replace `rnStopOkStarted` (the server theorems' vacuous premise) by a proof or a
   gated axiom.
5. **The generated tester**: specs in the canonical form (pure `Pre`/`Post` on records) evaluated
   by Lean over Go call sequences, generalizing `etc/spec-test/bbolt`.
6. **The stuck-code smoke test** and the **inventory** generator (call graph, classification,
   function-level diff for re-verification).
7. **The context bundle** for review rounds (`etc/gen-interface.py`'s rendering plus call sites
   and the last diff).
8. **The orchestrator** (`Workflow` script, `state.json`, the scheduler, budgets) and the report
   generator.

## Testing the skill

1. **Blind replay on proved code**: run it on code this repository verified by hand, from its
   driver alone, without its specs. First the logkv family (`examples/lintest/logkv*`: a fresh
   agent took about 112 minutes by hand, the variants 8 to 19, so the skill's overhead is measured
   against a known baseline); then `pkg/wait` or `idutil`, then the btree (sequential, a real data
   structure), then the cache (concurrent). Compare with the history: time, spec revisions after the
   freeze, `sorry`s left, axioms, bugs.
2. **Re-verification**: re-run raft's proof at a new upstream revision (the commits after `b867cf13`
   on etcd-io/raft's `main`) from the current proofs: the function-level diff, the thaws, the time.
   The witness experiment (three days by hand, 16 defects of etcd-io/raft#168) is the baseline for a
   variant.
3. **A new distributed package**: the first run of Stage 2 without a human: a candidate is etcd's
   lease protocol (`lessor` and its keepalives through raft), or rafthttp's peer protocol, with a
   driver that checks lease safety under partitions.
4. **Measured**: zero human interventions during the run (the requirement); spec revisions after the
   freeze; refuted axioms that reached Stage 5 (should be zero); mutation score of the drivers;
   the costs; and whether a human reading the report afterwards reverses any adjudicated decision
   (each reversal becomes a sharper gate, as review misses become principles).

## Risks

- **Axioms without a human.** The largest. The gates (tester, refuter, upstream tests, a body-first
  rule, no axiom of the package's own code) caught every false axiom of the history that had a Go
  execution (31 of 44); the 13 unobservable ones (framed-out writes, proposals without a permit) are
  why the frame check and the refuter's Lean side exist. A run's report lists the axioms first.
- **A driver too weak.** A theorem about a weak test is true and useless. Mutation testing and
  adequacy coverage are the answer; their thresholds are the run's input, reported.
- **Adjudicated design forks.** A wrong choice before the freeze costs statements; after, proofs.
  The ranking prefers the options that change nothing proved; the batch review afterwards is where
  a human corrects it.
- **Cost.** A raft-sized run is days of agents and builds of hours (the full build is 21 minutes to
  an hour). Budgets bound it; the report makes it visible.
- **Perennial gaps.** A run cannot change Perennial; a translator or library gap becomes an axiom
  (gated) or a `sorry`, and an entry for a human to take to Perennial.
