# Plan: a closed proof that raft's traces pass its own TLA+ trace validation (draft, 2026-11-08)

Branch `trace-check`. Background, harness, transcription and its checks:
`notes/raft-trace-validation.md`. Status: **draft**, to be reviewed, then frozen before proofs
start (the repository's practice: `notes/spec-first-plan.md`); amendments after the freeze are
dated, below the section they amend.

## Decisions (the user's, 2026-11-08)

- **Fully closed**, as the porcupine examples: `Main` runs the concurrent harness, then the
  checker on the recorded trace, and panics unless the checker accepts; the theorem is adequacy:
  no execution of `initialize'(); Main()` panics.
- **The direct checker** (`CheckTrace`'s search) is the one verified, not porcupine (the trace is
  totally ordered: porcupine's search reduces to it). Porcupine stays a cross-check outside the
  proof.
- **TLC's verdict, invariants included**: the checker accepts only when some behavior of the trace
  specification steps through every line, the search never branches (TLC's `TraceMatched`), no
  evaluation fails, and every state reached satisfies the eight invariants of
  `Traceetcdraft.cfg`.
- **Not tied to the workload**: the facts about raft are proved once, under premises on how the
  application uses raft; only the harness's layer is about its workload.
- **The raft verified is its `with_tla` build** (the trace hooks' bodies), translated from the local
  fork commit `e8f9566` (`etc/fork-patches/`) until it is pushed.

## The statement

`raft_tracecheck_safe` (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Results.lean`,
the shape of `raft_kv_porcupine_safe`): every execution of `kvProgram`'s analogue -- the package's
initialization, then `Main()` -- from a fresh state, of fewer than `2^k` steps, has no stuck
thread and no panic.

`Main()`: start a cluster as `RunConcurrent(DefaultCConfig(seed))` does (three voters, proposals,
drops, delays and reordering, isolations; no restart, compaction or configuration change); stop it;
convert its events (raft's `TracingEvent`s, in memory, no JSON) to the checker's; run `CheckTrace`;
panic unless `TLCOK`. The seed is fixed or read from a source the proof treats as arbitrary.

What it means, through the checker's spec (proved, not trusted): the trace of every execution is
accepted by `TraceAccepts`, the Lean transcription of `Traceetcdraft.tla`'s `TraceSpec` with TLC's
`TraceMatched` and the invariants; `Results.lean` states that as a corollary of the checker's spec.

## Trust base

- The Lean transcription of `etcdraft.tla` and `Traceetcdraft.tla` (`TraceAccepts` and what it is
  written in): the statement's meaning. Checked as the Go transcription was: executable, run on the
  same traces and mutants as TLC and the Go checker, verdicts and failing lines compared; reviewed
  against the TLA+ text by an independent reviewer.
- Goose and Perennial (as everything here); the standard-library specs the code uses
  (`strconv.FormatUint`, `time.Sleep`, `sync`, maps).
- The equivalence of the `with_tla` build verified and the no-op build etcd ships (no logger: the
  hooks return at once), argued, not proved.
- Not trusted: the Go checker, the harness, raft, the hooks' event construction (all verified).

## The layers

### A. The trace hooks and the logger (raft)

Each of the eleven hooks (`Spec/go_etcd_io/raft/v3/trace*.lean`, now "a no-op") gets a spec:
reading `r.traceLogger`; nil: no-op; otherwise the logger's `TraceEvent` called with the event of
the raft state at that point (a pure function of the abstract state: term, vote, commit, role, log
length, configuration, the message's fields). The logger is a `TraceLogger` interface value whose
spec the raft invariant carries (as other callbacks' specs are carried): a logically atomic update
`TraceEvent(ev)` whose linearization point appends `ev` to the trace. Callers' proofs change only
where the raft invariant changes (the logger field and its spec). Existing results: no logger.
`traceReceiveMessage`'s `time.Sleep(1ms)`: Perennial's spec.

### B. The simulation (raft, workload-agnostic)

A global ghost state holds the trace so far and the trace specification's state `σ` (the Lean
`etcdraft` state). At each event's linearization point (in the logger, under its lock), with
every node's raft ghost state (the existing protocol ghost, `StepR`'s `PState`s, which an invariant
relates to `σ`): `StepLine σ line` has exactly one successor `σ'` (no branching), `σ'` satisfies
the invariants, and the relation holds again. The relation `R(raft ghost, σ)`:

- per node: term, vote, role, log, commit index, configuration; `matchIndex` against the leader's
  progress `Match`; `votesResponded`/`votesGranted` against the vote tally; `durableState` against
  what the last `Ready` handed out;
- the message bags: `pendingMessages` the messages raft has queued (logged as sent) and not yet
  handed out in a `Ready`; `messages` those handed out and not yet received (dropped ones stay:
  the specification's network keeps them), against the protocol ghost's message knowledge.

Premises (the application's use of raft, discharged by layer D): no restart; no compaction (so
raft never sends a snapshot: a fact about raft's code, that it sends one only for entries missing
from storage); configuration changes only those the specification models (none, for the first
harness); the bootstrap (`StartNode` of every voter) before anything else, so the trace's
bootstrap lines are its first segment and `TraceInit` is determined by it.

Determinism (no branching) is part of the step: each line selects one specification action and
one message. A received message: two messages in the bag matching the line are equal (the fields
the line does not log are determined: a heartbeat response's `mmatchIndex` is 0, a rejection's 0).

The invariants: from the existing safety results (leader completeness, log matching, election
safety, `Protocol/Facts`), restated on `σ` through `R`; `MoreUpToDateCorrectInv`,
`QuorumLogInv`, `CommittedIsDurableInv` may need more.

### C. The checker (Go, verified against the Lean transcription)

The transcription is split for the proof: the core (`etcdraft`: the specification, the trace
semantics on in-memory events, `CheckTrace`) in Goose's subset without `fmt`, `strings.Builder`,
`encoding/json`, `sort.Slice` (structural equality or a hand-written encoding for the view's
keys, sorted slices by `slices.Sort` or insertion); NDJSON reading and the porcupine model in
packages of their own, not translated. Its spec: `CheckTrace(events)` returns `TLCOK` exactly when
`TraceAccepts(events)` (sound and complete; the evaluation errors are failures). Size: the Go is
about 1,500 lines; the proof is mostly the actions' functional correctness against their Lean
counterparts, and the search's.

### D. The harness and Main (the workload)

The concurrent harness (`concurrent.go`, its Goose translation needs no change): each replica a
`raft.Node` with its application goroutine, the network's goroutines, the drivers, the locked
recorder. Its proof uses the node API's specs (`StartNode`, `Node.Step`, `Ready`, `Advance`,
`Tick`, `Propose`, `Status`, `Stop`, `ReportUnreachable`) and discharges layer B's premises (it
never restarts, compacts or proposes a configuration change). The recorder's lock invariant holds
layer B's ghost state: its `TraceEvent` is the logger spec's linearization point. `Main`'s proof:
the checker's spec and layer B's invariant at the end (the whole trace accepted).

## Order of work

1. **S1 the Go for the proof**: the package split (C), the core rewritten without `fmt` and
   friends, a `Main` for the closed program, `etc/goose.py` projects for the harness and the core;
   the differential tests kept as the regression check.
2. **S2 the Lean transcription**: pure, executable; added to the three-way comparison (four with
   it); reviewed.
3. **S3 the hooks' and logger's specs** (A): the `spec` skill's process; the eleven proofs; raft's
   invariant carries the logger; raft and its dependents rebuilt.
4. **S4 the simulation on paper** (B): `R`, each hook's correspondence, determinism, the invariants'
   mapping; reviewed; this plan amended and frozen.
5. **S5 the simulation in Lean** (B).
6. **S6 the checker's proof** (C).
7. **S7 the harness, `Main`, adequacy** (D), `Results.lean`, `etc/tcb-report.py` collection.

S1, S2 and S3 are independent of each other. S4 needs S2's definitions (and S3's event function).

## Risks

- **`TraceInit` reads the whole trace** (`TraceServer`, the bootstrap lines up to each server's
  first other line): handled by the bootstrap premise (the bootstrap segment comes first and
  determines it); a server added later (configuration changes) would need more.
- **Determinism** may fail for a line the analysis missed (two matching messages differing in an
  unlogged field); none of the recorded traces branches.
- **The invariants**' mapping: `MoreUpToDateCorrectInv` (every pair of servers' logs) and
  `QuorumLogInv` are strong; if one does not follow from the existing results, the plan is
  amended (prove it at the protocol level, or the user's decision to drop it).
- **`matchIndex` vs `Progress.Match`**: they agree while no member is removed and re-added (the
  fourth gap of `notes/raft-trace-validation.md`); to check on paper for every place raft resets a
  progress (`becomeLeader`, `ResetState`).
- **The fork commit unpushed**: the branch cannot land until it is.

## Open questions for the user

- The step bound `2^k` and the seed (fixed, or arbitrary as `primitive.RandomUint64`'s).
- Whether the TLC comparison (needs Java and the TLA+ tools) runs in CI or stays a local check.
