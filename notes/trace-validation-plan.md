# Plan: a closed proof that raft's traces pass its own TLA+ trace validation (draft, 2026-11-08)

Branch `trace-check`. Background, harness, transcription and its checks:
`notes/raft-trace-validation.md`. Status: **Scope settled (2026-11-08); Draft next.** The stage follows
`notes/spec-first-plan.md`'s phases (Scope, Draft, Review, Test, Probe, Freeze, Prove; no proof
before the user's freeze, the tag `trace-check-frozen`); amendments after the freeze are dated,
below the section they amend.

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

## The gates, delegated (the user's, 2026-11-08)

`notes/spec-first-plan.md`'s order stands (Draft, Review, Test, Probe, Freeze, Prove; no proof
before the freeze), with the user's gates delegated to the agent for this stage:

- **Review** is run by the agent: fresh `spec-reviewer` rounds on the Draft until a round leaves
  nothing first-tier, each repair followed by another round.
- **Freeze**: when Review is clean (and Test and Probe done), the agent freezes: the annotated tag
  `trace-check-frozen` on the frozen commit, recorded here as "frozen by the agent under the
  user's delegation", with the round that cleared it; then Prove.
- **Still the user's**: pushing anything (the fork commit, the branch) or any other action outside
  this repository; a change to the trust base (a new axiom or model assumption, the transcription
  trusted) or to the closed theorem's statement (dropping an invariant, narrowing the workload).
  The agent records such a question in "Questions for the user" below, takes the plan's
  recommendation where it has one (marked "taken by the agent, pending the user's veto"), and
  goes on with the work that does not depend on it; it does not stop for them.
- Every other decision the agent takes is recorded where it is taken, "decided by the agent",
  with the options and the reason (`notes/spec-first-plan.md`, "Who decides").

## Questions for the user

- **Q1 (2026-11-08, S3): a new premise on raft's constructors.** `NewRawNode`, `StartNode`,
  `RestartNode` (and the internal `newRaft`, `setupNode`) take `TraceLoggerOk cv.TraceLogger'` as
  their last premise (the configuration's trace logger satisfies the logger contract; in increment
  1, `TraceLoggerOk tl := tl = nil`), discharged for a nil logger (every client today) by `rfl`.
  Alternatives: a second constructor spec (a spec family, forbidden), or the premise hidden in
  `ConfigValid`. Taken by the agent, pending the user's veto: the premise
  (`notes/trace-validation-hooks.md`). Its consequences (done, 2026-11-08): the examples'
  configuration predicates (`kvreconf`'s `CfgOk`, `kvdurable`'s `kdCfgOk`) gain the conjunct; the
  etcd server's `rnStartCfg` gains the field `traceLogger`, so `bootOk` (`NewServer`'s premise on
  `bootstrap`'s result, a premise of an exported result) says it too: true of the code
  (`raftConfig`, `bootstrap.go`, sets no trace logger).
  Review round 1 of S4 (S6): increment 2 replaces `TraceLoggerOk` by `isTraceLogger γt tl`, an
  `IProp` with a ghost name, so this premise changes again (inside the triple, `γt` a new binder);
  whether to take increment 2's shape now is open in `notes/trace-validation-sim.md`.
- **Q3 (2026-11-08, S4 review round 1): two changes to the harness `Main` runs.** Without them the
  closed theorem is false: (F1) the harness sent a `Ready`'s messages before `Advance`, and since
  raft logs the `Ready` only after handing it out (`traceReady` ends `acceptReady`, which runs
  after the hand-off), a receipt could be logged before its sender's `Ready` line, which the trace
  specification cannot follow (witnessed by the reviewer with a sleep in the window); now it sends
  them after `Advance`, which the run loop takes only once `acceptReady` has returned. (F3) Goose's
  semantics ignores delays, so it allows unboundedly many elections, each appending an entry, and
  a batch cut by `MaxSizePerMsg` (1 MiB) carries a commit index past its last entry (gap 5): now
  `MaxSizePerMsg` is unlimited. Both narrow nothing the specification can check (the old send
  order's extra behaviors are the ones it rejects; an unlimited batch is raft's `noLimit`), and
  `Main`'s workload is otherwise unchanged. Alternatives: raft's instrumentation changed to log the
  `Ready` before the hand-off (a fork change beyond the build tags), for F1; none for F3 short of a
  proof bound on elections. Taken by the agent, pending the user's veto
  (`examples/raft/tracecheck/concurrent.go`; the tests pass, 10 seeds, and the reviewer's F1
  witness passes with the change; `nonissues/raft-trace-ready-logged-after-handout.md`).
- **Q4 (2026-11-08, S4 review round 2, N1): the closed statement is false as planned:
  `LeaderCompletenessInv` is not an invariant of raft, nor of `etcdraft.tla`.** A stale leader (no
  check-quorum: it keeps leading its term until it hears of a later one) lacks an entry committed
  in a later term (`notes/raft-trace-validation.md`, item 7; `gaps_test.go`,
  `TestGap7LeaderCompleteness`; TLC: "Invariant LeaderCompletenessInv is violated"). Message
  delays alone reach it, so no harness excludes it, and `Main` with the invariants checked can
  panic. Options: (a) check the other seven invariants only (the checker's `invariants` list, Go
  and Lean, and the statement's meaning: upstream's `Traceetcdraft.cfg` minus one); (b) correct the
  invariant's guard in both transcriptions (a leader of a term at least the committing server's,
  `currentTerm[l] >= currentTerm[i]`: the transcription then departs from upstream's text there, a
  trust question; the corrected invariant not yet checked on traces or proved); (c) turn
  check-quorum on (a stale leader then steps down; not modelled by `etcdraft.tla`, so it brings
  its own gaps). **Not taken** (no recommendation in the plan; the statement's and the trust
  base's). The agent's recommendation: (b) if the corrected guard survives the traces and a
  review, else (a); either way, report item 7 upstream (the user's: outside this repository).
  Evidence for (b) (2026-11-08, a scratch copy, not committed): with the guard
  `vl.CurrentTerm > entry.Term && vl.CurrentTerm >= s.S[i].CurrentTerm` in the Go transcription,
  `TestGap7LeaderCompleteness`'s trace is accepted and 30 concurrent seeds and the deterministic
  traces still pass; the argument: every committed entry server `i` knows was committed at a term
  at most `currentTerm[i]`, and a leader of a term at least that holds it (leader completeness,
  or it is the committing leader).
- **Q5 (2026-11-08, S4 review round 2, N2): three voters do not exclude gap 6.** A leader's own
  `MsgVote`, delayed past its first heartbeat to a voter, is refused by raft (`lead != None`) and
  granted by the specification (`TestGap6ThreeVoters`; TLC rejects at the same line), so `Main`
  can panic. Options: (a) the harness's network delivers each link's messages in order (FIFO per
  sender-recipient pair; drops and delays stay, reordering only across links): with three voters a
  voter then hears of a leader only after the leader's `MsgVote`; (b) add raft's `lead` to the
  specification's vote condition (the transcriptions depart from upstream's text: a trust
  question). **Not taken** (no recommendation in the plan; (a) narrows the workload, (b) changes
  the trusted transcription). The agent's recommendation: (a), with the argument proved in layer B
  as premise P9 restated ("a voter learns of its term's leader only after the leader's
  `MsgVote`, or not at all").
  Evidence for (a) (2026-11-08, a scratch copy, not committed): a per-link FIFO `send` (one
  goroutine per link, delays and drops kept) passes 20 concurrent seeds (weak: random runs did not
  reach N2 before either; the argument is what counts).
- **Q6 (2026-11-08, S4 rounds 3-4; to present with increment 2's draft): new client-owned ghost
  on raft's node API, gated on a traced cluster (`γ.raft.reTrace = some γt`).** The simulation needs (1) a token per
  handed-out traced message (`Advance`'s post gives them, `Node.Step` takes one,
  given back on a timeout), (2) a proposal budget (`Propose` takes a credit; the leader's
  inflights then never fill, P5), (3) `isTraceLogger γt …` in the constructors' premise (Q1's
  final shape), (4) since round 5: each message token's position on its link (P9 through the
  FIFO network, if Q5 (a)), and gated premises on the constructors for layer B's other
  premises (the configuration, no `RestartNode`, no `ProposeConfChange`, each `StartNode` with its
  node's piece of the allocation and the allocation's peers), (5) since round 6: an exclusive
  per-link cursor for the tokens' order, a compaction permit never handed out, the budget's gate
  (non-empty data), no `TransferLeadership`/`ReadIndex`/`Campaign`/`ForgetLeader`
  in a traced cluster, (6) since round 7: the allocation law's premises `|peers| ≤ 3` (P9's voter
  count) and a non-`dup` cluster, the compaction permit as a gated conjunct of the storage bound
  `storBnd`, (7) since round 8: the gate a cluster field `reTrace` of raft's names (as `dup`, so
  untraced clients need no witness), and with it, `Ready`'s snapshot empty, (8) since round 9:
  `storBnd` exempting `c = 0`, `StartNode` tying its logger to `reTrace`, `RestartNode` taking an
  untraced cluster, the allocation in three steps, raft's `reNoSnap` mode revived as
  `reTrace.isSome`. Untraced clients (every existing one) carry one new pure fact,
  `⌜γ.raft.reTrace = none⌝`, from a law raft exports. The spec skill makes each the
  user's; they will be presented side by side with the current specs once increment 2 is drafted
  (`notes/trace-validation-sim.md`, "Increment 2").
- **Q2 (2026-11-08, S3): raft's results rest on `strconv.FormatUint`'s axiom.**
  `traceChangeConfEvent` formats the change's ids (`strconv.FormatUint`) before its nil check, so
  the translated raft calls it even without a logger, and raft's linked results now rest on
  `Spec/strconv/FormatUint.lean`'s trust-boundary axiom (already the server's). The plan's "Trust
  base" lists `strconv.FormatUint` among the standard-library specs: taken by the agent as that
  recommendation, pending the user's veto (`etc/tcb-collections/raft.txt` updated, and `kv`, `kvdurable`, `kvreconf`, whose results reach raft's; the server's collections already had it). The
  alternative, an early `if r.traceLogger == nil { return }` in the fork, changes raft's code beyond
  the build tags.

## The statement

`raft_tracecheck_safe` (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Results.lean`,
the shape of `raft_kv_porcupine_safe`): every execution of `kvProgram`'s analogue -- the package's
initialization, then `Main()` -- from a fresh state, of fewer than `2^k` steps, has no stuck
thread and no panic.

`Main()`: start a cluster as `RunConcurrent(DefaultCConfig(seed))` does (three voters, proposals,
drops, delays and reordering, isolations; no restart, compaction or configuration change); stop it;
convert its events (raft's `TracingEvent`s, in memory, no JSON) to the checker's; run `CheckTrace`;
panic unless `TLCOK`. The seed is arbitrary (`primitive.RandomUint64`, which the proof treats as
any value: the theorem covers every seed); the step bound as the kv examples' (`n < 2^61`) unless
the proof needs another (the user's, 2026-11-08).

`Results.lean` also states, as a corollary of the checker's spec, that the trace of every
execution is accepted by `TraceAccepts`, the Lean transcription of `Traceetcdraft.tla`'s
`TraceSpec` with TLC's `TraceMatched` and the invariants.

## Trust base: one transcription of the TLA+, either one (the user's, 2026-11-08)

What the result says about raft rests on one transcription of `etcdraft.tla` and
`Traceetcdraft.tla` deciding what the TLA+ decides -- either one, not both:

- the **closed theorem** mentions only the Go program (`Main`, with the Go checker in it) and
  Goose's semantics: its meaning rests on the Go checker's faithfulness to the TLA+; the Lean
  transcription is a device inside the proof, and a mistake in it would leave the theorem as true
  and as meaningful;
- the **corollary** is stated with the Lean `TraceAccepts`: its meaning rests on the Lean
  transcription's faithfulness, the Go checker being a verified implementation of it.

Layer C proves the two equal (`CheckTrace` accepts exactly when `TraceAccepts` holds), so the
evidence for either is evidence for both: the Go transcription's three-way comparison with TLC (the
state spaces under four bounds, clean, mutated and full-featured traces, verdicts and failing lines)
and the independent review (`notes/raft-trace-validation.md`) count for the Lean one once the
checker's spec is proved. "Faithful" is the one question: that the transcription computes what the
TLA+ says (not that raft or the harness are right: those are verified).

The rest of the trust base:

- Goose and Perennial (as everything here); the standard-library specs the code uses
  (`strconv.FormatUint`, `time.Sleep`, `sync`, maps).
- The equivalence of the `with_tla` build verified and the no-op build etcd ships (no logger: the
  hooks return at once), argued, not proved.

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
2. **S2 the Lean transcription**: pure definitions, read side by side with the TLA+ text. Not a
   trust question (above): a Lean definition differing from the Go makes the checker's proof (S6)
   fail. An executable version run against TLC would only find such a difference earlier;
   optional.
3. **S3 the hooks' and logger's specs** (A): the `spec` skill's process; the eleven proofs; raft's
   invariant carries the logger; raft and its dependents rebuilt.
4. **S4 the simulation on paper** (B): `R`, each hook's correspondence, determinism, the invariants'
   mapping; reviewed; this plan amended and frozen.
5. **S5 the simulation in Lean** (B).
6. **S6 the checker's proof** (C).
7. **S7 the harness, `Main`, adequacy** (D), `Results.lean`, `etc/tcb-report.py` collection.

S1, S2 and S3 are independent of each other. S4 needs S2's definitions (and S3's event function).

## Draft: S2 done (2026-11-08)

The Lean transcription, `Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/etcdraft/Tla/`
(`Types`, `Spec`, `Invariants`, `Trace`, `Check`; namespace `Perennial.EtcdGrove.Etcdraft`): all of
`etcdraft.tla` (every action, the five next-state relations, the invariants) and `Traceetcdraft.tla`
(the trace's constants, the `IfLogged` actions, `TraceNext`, `stepLine`), and `checkTrace`,
`Result.tlcOK`, `traceAccepts` (the corollary's statement), mirroring the Go function by function.
Decided by the agent (the options and the reasons, `notes/spec-first-plan.md`, "Who decides"):

- numbers `Int` (TLA+'s), not 64-bit words: the statement's meaning stays TLA+'s, and the
  checker's proof (S6) carries the bounds the Go's `int` needs (the workload's terms and indices);
- servers `Nat`, sets sorted duplicate-free lists, the bag a list of messages with counts, as the
  Go's: `=` on values is derived structural equality, decidable, so the definitions run, and S6
  relates like to like;
- where TLC fails evaluating, `EvalM := Except EvalError` (the Go panics and `CheckTrace`
  recovers);
- `stepLine`'s loop takes fuel (`lineFuel`: the steps one line can take), which Lean's termination
  needs and the Go's loop does not; S6 shows the fuel is never exhausted.

Checked by running it (`#eval`, through `cmd/leanexport`, which writes a trace as a Lean file): on
16 traces (the five clean seeds, the four mutants, five full-configuration traces, two concurrent
ones) its verdict and failing line equal the Go checker's (and so TLC's), and on the
evaluation-error witness (a commit index past the log) it fails with the same error. Not part of
the trust argument (the plan's "Trust base"): S6's proof is what ties it to the Go.

## Draft: S4 drafted (2026-11-08), in Review (rounds 1-9 done; blocked on Q4, Q5, Q6)

`notes/trace-validation-sim.md`: the abstraction `α` (a server's variables, the messages, the bags
as new ghost state with a token per message in flight), the relation's phases (idle, handling a
received message), determinism line by line, the invariants (two routes), the premises P1-P7 and
increment 2 of the hooks' specs. Found while drafting it: a fifth place where `etcdraft.tla` does
not fit raft (an append request's commit index, `notes/raft-trace-validation.md`, item 5),
witnessed with `MaxInflightMsgs: 1`, not reached by `DefaultCConfig`: premise P5, discharged by the
harness's configuration, the statement unchanged. Review round 1 (a fresh `spec-reviewer`,
`notes/trace-validation-reviews/s4-r1.md`): four first-tier findings, two of them making the closed
theorem false with the harness as it was (Q3), a sixth gap (`notes/raft-trace-validation.md`, item
6: a voter that knows its term's leader; at most three voters, P9), the bags' phantom replies;
revision 2 of the note answers each. Round 2 (`notes/trace-validation-reviews/s4-r2.md`): two
first-tier findings that make the closed theorem false with `DefaultCConfig` (Q4: upstream's
`LeaderCompletenessInv` is not an invariant of raft; Q5: gap 6 with three voters), both the user's;
second-tier ones on the contract and the invariants' facts, answered by revision 3. The Review
cannot clear, so no freeze, until Q4 and Q5 are decided. Round 3 (`notes/trace-validation-reviews/s4-r3.md`): the logger
contract must hand over the event (A1), and `MoreUpToDateCorrectInv` is not raft's either (A2:
`notes/raft-trace-validation.md` item 8, TLC confirms; five voters and cut batches, so not reached
by `Main`: P5 strengthened, the statement unaffected); second tier on the invariants' facts, the
bootstrap, `Advance`'s stopped branch, the phase threaded through raft's internal functions, the
tokens' key; revision 4 answers each. Round 4 (`notes/trace-validation-reviews/s4-r4.md`): no further behavior the
specification cannot follow (with Q4's guard and Q5's FIFO network); the inflight bound is a
workload bound raft cannot see (a proposal budget: Q6), the bootstrap mode replaced by a per-node
flag, the invariants' clauses and routes corrected; revision 5. Round 5 (`notes/trace-validation-reviews/s4-r5.md`): none
either; the tokens need their link position for P9, layer B's other premises must enter through
gated API premises (both Q6), `QuorumLogInv` is not raft's (a copy of raft's `histsOk`); revision 6. Round 6 (`notes/trace-validation-reviews/s4-r6.md`): none either;
two more API gaps (P2's compaction, the tokens' order needs an exclusive cursor), both Q6; the
reviewer saw nothing else blocking a freeze once Q4-Q6 are decided; revision 7. Round 7 (`notes/trace-validation-reviews/s4-r7.md`): one
first-tier finding, P9's voter count with no channel into raft (a premise of the allocation, Q6);
second tier on the storage bound, the cursor's ownership, `QuorumLogInv`'s clauses; nothing else
blocking once Q4-Q6 are decided; revision 8. Round 8 (`notes/trace-validation-reviews/s4-r8.md`): round 7's
repairs right; one first-tier gap (`Ready`'s snapshot under the gate: Q6), second tier on the gate's
place, the inherited commit, the leader's own `Match`, the hand-off clause; revision 9. Round 9 (`notes/trace-validation-reviews/s4-r9.md`): two
one-sentence first-tier gaps (`storBnd`'s `c = 0`; the gate half moved to `reTrace`), the
allocation's order, untraced clients' pure fact, `reNoSnap`; revision 10.

## Draft: S3 increment 1 done (2026-11-08)

The hooks' design, its open points (the call sites, the update's ghost: settled with S4) and
Q1: `notes/trace-validation-hooks.md`. Increment 1, the nil-logger half, is in: the thirteen specs
(the eleven hooks, `traceEvent`, `traceNodeEvent`) and proofs, the field and `TraceLoggerOk` in
raft's invariant, the call sites, the constructors' premise (Q1) and its clients; raft's build
green again (`notes/decisions.md`, "The trace hooks' specs, increment 1: no logger"). Increment 2,
the logger's contract, waits for S4 (what the hook hands the logger, the update's ghost).

## Draft: S1 done (2026-11-08)

- `examples/raft/tracecheck` is a Go module of its own (`go.mod` replaces raft by the local fork
  checkout `.lake/raft-trace`, until the fork commit is pushed: then its pseudo-version and an entry
  of `etc/goose.py`'s `GO_MOD_PINS`); project `tracecheck` of `etc/goose.py` translates its packages
  `.` (the concurrent harness and `Main`) and `./etcdraft` (the checker core) into the main tree.
  Both translations build (`lake build` of their Code and GeneratedProof modules, 2026-11-08).
- The checker core (`etcdraft`) uses on its proved paths only slices, maps, structural equality
  and panics (`EvalError`, recovered in `CheckTrace`): no `fmt`, `strings`, `sort` or hashing (those
  only in `String`/`Error` methods); a hand-written decimal parser for ids; typed `TraceError`s.
  The NDJSON reader moved to `etcdraft/ndjson`, the porcupine model (and a canonical state key, for
  porcupine's hashing and the state-space test) to `etcdraft/pmodel`; neither is translated.
- `Main` (`main.go`): `RunConcurrent(DefaultCConfig())`, then
  `ConvertEvents` (raft's events to the checker's, in memory, as the NDJSON path reads them:
  `TestConvertMatchesNDJSON`), `NewTrace`, `CheckTrace(tr, true).TLCOK()`, panic otherwise.
  `TestMainRuns` runs it.
- The harness's files Goose sees (`concurrent.go`, `main.go`: `with_tla || goose`) draw their
  random choices from `primitive.RandomUint64` (as the other harnesses: `below`, as
  `examples/raft/kvreconf`'s), so the configuration has no seed, and use no `encoding/json`
  (Perennial models neither it nor `math/rand/v2`); the deterministic driver and `WriteNDJSON`
  (`sim.go`, seeded `math/rand/v2`) are `with_tla && !goose`, the tests `with_tla`.
- Not yet: the generated initializers (`etc/gen-init.py`) and links of the two packages, which come
  with their specs (the rest of Draft).

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

## Settled questions (the user's, 2026-11-08)

- The seed: arbitrary (`primitive.RandomUint64`); the step bound as the kv examples'.
- The TLC comparison (needs Java and the TLA+ tools) stays a local check (`TestAgainstTLC` skips
  without `TLA_TOOLS`), not in CI.

## The phases of this stage (`notes/spec-first-plan.md`)

- **Scope**: this plan (settled 2026-11-08).
- **Draft**: every statement written, proofs `sorry`, links generated, the glue proved: S1 (the Go
  the specs are of), S2 (the definitions they are written in), S3 (the hooks' and logger's specs,
  with the glue in raft's callers), and the statements of layers B, C and D (the simulation
  invariant and step lemma, `CheckTrace`'s spec, the harness's functions' and `Main`'s specs, the
  closed theorem). S4's paper sketch is part of Draft (it is what B's statements are written
  from).
- **Review**: fresh `spec-reviewer` rounds on the Draft (the specs, the invariant, the closed
  statement), until nothing first-tier is left; the questions batched to the user.
- **Test**: the specs against runs (the harness's traces, the hooks' events against the
  transcription's states).
- **Probe**: an easy proof (a hook) and a hard one (a step of the simulation: a received append).
- **Freeze**: the user's; the tag `trace-check-frozen`.
- **Prove**: S5, S6, S7 and the rest.
