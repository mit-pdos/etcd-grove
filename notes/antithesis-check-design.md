# Raft against Antithesis's TLA+ model: design (#33, S0)

Stage S0 of mit-pdos/etcd-grove#33 (2026-11-23; branch `antithesis-check`). The goal: a closed,
proved robustness theorem saying a Go program never panics, where the program runs a cluster of
the verified raft, records Antithesis-format step reports, checks them with a Go transcription of
Antithesis's TLA+ model and trace binding, and panics unless the stream is accepted. This note is
the design, for review before plumbing (S2-S4). S1, the Go checker, is done
(`examples/raft/antithesis/check`, below). Nothing here is Lean; every Lean statement is a text
sketch, not typechecked.

The four decisions of #33 are approved (2026-11-23, the user's, via the coordinator): our harness,
not Antithesis's `rawnode/`; raft's main build (no `with_tla`); scope inside what their model proves
safe (synchronous storage, one atomic write per `Ready`, no `AsyncStorageWrites`, PreVote,
CheckQuorum and leader transfer off at first); the TLA+ vendored under `third_party/`.

Sources: antithesishq/etcd-raft-formalized at `b3c7c16` (`third_party/etcd-raft-formalized/`,
which vendors `EtcdRaft.tla`, `EtcdBinding.tla`, `TraceKit.tla` and the binding's configurations;
cited below as R, B, TK with line numbers). Prior art: the trace check of upstream raft's
`etcdraft.tla` (`examples/raft/tracecheck/`, `notes/trace-check-design.md`, `raft_tracecheck_safe`
in `RaftTla/Proof/.../tracecheck/Results.lean`).

## 1. The closed statement (sketch)

Modelled on `raft_tracecheck_safe`. Program `antithesisProgram` = `Main` of package
`examples/raft/antithesis` (S2):

```go
func Main() {
	c := RunCluster(DefaultConfig)          // N RawNodes, one goroutine each; network goroutines; bounded run
	v := check.Run(&check.Config{Server: c.Servers, InitVoters: c.Servers, Bootstrapped: false}, c.Events())
	if v.Kind != check.Accepted { panic("rejected") }
}
```

```
theorem raft_antithesis_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : ...antithesis.Assumptions] (Hprem : ∀ hG, ⊢ antithesis.premises)
    (σ g) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (n) (Hn : n + 4 ≤ 2^61) (κs t2 σ2)
    (Hsteps : RealNstepsBelow (2^31) n ([antithesisProgram], (σ, g)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2 ∈ t2, RealNotStuck e2 σ2) ∧ (∀ e2 ∈ t2, ¬ UnrecoveredPanic e2)
```

and its `Robust` instance in `Spec/.../antithesis/TopLevelRobustness.lean` (no crashing machine:
one process; a restart, if the harness has them, is in-process, §6 Q2). The program-level corollary,
the analogue of `raft_tracecheck_accepts`:

```
{{ isPkgInit antithesis ∗ antithesis.premises }} RunCluster DefaultConfig
{{ c, RET c; WP c.Events() {{ v, ∃ sl L, v = #sl ∗ eventsRep sl L ∗ ⌜AntCheck.Accepts cfg3 L⌝ }} }}
```

where `AntCheck` (S3) is a Lean transcription of `EtcdBinding.tla` as a function (it is
deterministic, §3): `AntCheck.run cfg L : Verdict`, and `check.Run`'s spec says it returns that
verdict (panicking exactly where `AntCheck.run` is an evaluation error). `AntCheck` is an
intermediate, not trust base: the robustness statement names only the Go program. What the theorem
*means* (an accepted stream is a behaviour of `EtcdRaft.tla` whose TLAPS/Veil invariants then hold)
rests on (i) `check` being a faithful transcription of the binding (evidence: §4's differential test
and review against the cited lines), and (ii) Antithesis's own argued, not checked, claim that each
binding step is a sequence of `EtcdRaft` steps and `Safe` implies the model's properties
(their spec/README, "Assumptions and limitations", last item).

## 2. Constants and reports

**Configuration.** `EtcdBindingEmpty.cfg`: `Server = InitVoters = {"raft1","raft2","raft3"}`,
`Bootstrapped = FALSE` (the model's `Init`, R 181-201: empty logs at term 0), `Values = {"v"}`,
`Nil = ""`, invariants `ElectionSafety`, `OneVotePerTerm`, `Safe`. Recommended over the
bootstrapped configuration (§6 Q1): `BootInit` (B 733-753) is the state after a first election
whose leader appended one entry of type `"config"`, which `rawnode` writes into the storage before
starting raft (`rawnode/node.go` `Start`, data `"boot"`); raft's own `RawNode.Bootstrap` writes one
conf-change entry per peer at term 1, which matches neither initial state and would be rejected at
the first `boot` report (`lastIndex` 3, not 0 or 1). With `Bootstrapped = FALSE` the nodes start
from a storage whose `InitialState` reports the voters (`ConfState{Voters: 1,2,3}`) and no entry,
as `rawnode` does with `BOOT=0` (their `sim3-empty`, `sim5-async-empty` traces).

**Reports our harness emits** (the default mode of `rawnode/node.go`, its package comment and
`drain`): `boot` once per node at start (`term vote commit lastIndex lastTerm applied voters
outgoing`); then per input, on the node's goroutine: `recv msg` before `Step` of a message; for
each `Ready` until `HasReady` is false: `ready by role term vote commit first entries` announcing
the one atomic `Save` of `HardState`+entries (only if something is written or the role changed),
then `send by msg` per message (reported before it is handed to the network), then `apply by first
entries` before applying committed entries, then `Advance`. Entry and message encodings as
`rawnode`'s `entryOf`/`msgOf` (types `noop`/`command`/`conf`; message types `app hb vote appresp
...`). Not emitted in scope: `mem write wrote flush net made` (async, parallel, batch), `snap
restore conf readreq read`. The collector appends reports under one lock in the order emitted, so
a send's report precedes any receipt of it.

The checker transcribes the whole binding regardless (every report kind), so turning a mode on
later changes the harness and the proof, not the checker.

## 3. Nondeterminism

TLC "searches" nothing here. `Next0 == (GC \/ Step) /\ UNCHANGED read` (B 775), `Step` requires
`~GCDue` (B 767) and `GC` requires `GCDue` (B 714): at most one is enabled. Every action gives
every primed variable by an equality of a deterministic expression; the only CHOOSEs are `First`
(B 731, a fixed element of `InitVoters`), `K` (B 316, the least element of a set of integers) and
`LastConf` (R 161, the greatest). The composite steps `InMemory`/`OnDisk` are the binding author's
hand-written sequences of model actions (TraceKit convention 2, TK 25-26: "composite steps, no
search"); the binding header says it (B 22-23). So every state has at most one successor, TLC's
breadth-first frontier has at most one state per event, and the Go checker's loop (one state,
GC whenever due, then the event) reaches exactly TLC's states and verdict. Completeness with
respect to TLC is therefore not a search argument but the transcription's faithfulness; what is
*not* covered is the binding's own completeness with respect to `EtcdRaft.tla` (a report that some
model-step sequence explains but the hand-written composite does not): that is a false rejection
risk for the proof (§5), never a false acceptance.

TLC semantics the transcription reproduces, because they decide verdicts: conjunctions evaluated in
order with LET definitions evaluated where used (so evaluation errors arise at the same points); a
record constructor evaluated whole (`InMemory`'s result: an error in any field is an error even
when `ok` is false); `SubSeq`/indexing outside the domain, an absent report field, or a string
compared with a record are evaluation errors (Go panics with `EvalError`; `check.Check` reports
ERROR); CHOOSE over a set of strings picks the least; integers are 32-bit (the reader refuses
others, as `TraceKit.java`'s `getAsInt`); invariants checked on every new state, the first failing
of `ElectionSafety, OneVotePerTerm, Safe` reported, `VIOLATED k` at the event that made it. Not
reproduced: TLC's limit of 65,535 states per behaviour (the Go checker has none; it accepts longer
streams than TLC can check), and the exact error text.

## 4. Forgotten facts

`GC` (B 696-723, convention 4) is transcribed as is and taken whenever due, as TLC must. It only
removes facts every guard tests positively, so it can only disable steps: it is a source of false
rejection, never of false acceptance, and it is what keeps the checker's sets small. Keeping it
(rather than a checker without GC, which would accept a superset) keeps the checker
TLC-equivalent, which the differential test needs. If the proof finds a run of verified raft that
GC wrongly rejects, that is a finding about their binding (§5).

## 5. Where verified raft may be rejected (top risk)

The statement is false if some schedule of our harness over etcd-grove's raft (v3.7.0 + three
fixes, `etc/goose.py` `RAFT_REV` `d2c16c55`) produces a stream the binding rejects. Their raft is
upstream `main` at `99f9ffb` (after v3.7.0, with the single-voter read-index fix upstreamed). In
scope (sync writes, 3 voters, no snapshots, no membership change, no reads):

1. **Boot shape** (certain if done wrong): `RawNode.Bootstrap`'s conf entries or a boot entry not
   of `BootInit`'s shape are rejected at the first `boot`. Avoided by §2's configuration; needs a
   raft spec for `NewRawNode` on a storage whose `ConfState` names the voters and holds no entry
   (today's `NewRawNode.spec`: "an empty storage", conf state "possibly empty"; to check in S2).
2. **Follower commit rule** (`CommitBeyondConfirmed`, B 435-436; R 431-439, their "deliberate
   difference"): the model commits only within what the leader of the request's term confirmed.
   Raft commits to `min(m.Commit, last new index)` on an append and to `m.Commit` (the leader's
   `min(match, committed)`) on a heartbeat; both are within `confirmed` as long as `confirmed` tracks
   every ack the node made in that term, including across a restart (`confirmed` is ghost and is
   not reset by `Boot`). Their 12.8k simulator runs and ours (§7) never hit it. Low.
3. **Raft version**: differences between our pin and theirs (log shrinking removed upstream; our
   probe-shortcut and configuration-on-apply fixes) change when raft sends, not what: sends are
   checked against the leader log, which both have. The cheap test is S2 itself: run the harness
   under the Go checker on many schedules before any proof.
4. **Binding incompleteness** (§3): a report sequence that is a model behaviour but not the binding's
   hand-written composite (e.g. a `ready` whose write both truncates and acks in an order `OnDisk`
   does not take), or GC dropping a fact still needed (B 689-694). Unknown; their sut-mutants and
   sim runs found none in default mode.

Outside the initial scope, each a known difference:

5. **Logs are whole** (their limitation): with log compaction a node keeps a snapshot in place of a
   prefix; the binding handles it (`snap` has no model action, `SnapOk` checks a sent snapshot
   against the whole leader log), but a compacting harness adds `snap`/`restore` reports.
6. **Configuration at a snapshot's receipt**: `InMemory` takes a received snapshot's configuration at
   once (B 258-260, `RestoreConf`); our fork switches when the snapshot is applied
   (`issues/raft-snapshot-during-apply-stale-confchange.md`). With snapshots and membership changes
   the model's `config[n]` and raft's differ, and quorum/`Unpromotable` checks can reject. Likely
   rejection in that scope.
7. **Membership**: `Unpromotable` (B 274-275) and `Legal` (R 152) — raft refuses these too; risk only
   through 6.
8. **Read index** (`ReadIndexStale`, B 663-667): our fork's read-index fixes are upstream at theirs.

## 6. Which raft API the harness drives

(Asked by the coordinator, 2026-11-23.) **Recommendation: (a) `RawNode`, one goroutine per node, in
Antithesis's default mode** (one input, then drain `Ready`s; one atomic `Save` per `Ready` announced
by `ready`; send; apply), concurrency in the network goroutines and the drivers around the nodes.

Reasons:
- (b) cannot produce faithful reports without hooks inside raft. With raft's channel `Node`, one
  `Ready` follows several inputs, so only the batch reports fit, and `mem` must report raft's role,
  term, vote and commit *after each input* (`rawnode`'s `note` reads `RawNode.BasicStatus` between
  inputs on the goroutine that owns the `RawNode`). Behind `node.run` that state is not observable
  per input (`node.Status()` is served by `run` between its selects, after any number of inputs), and
  a `Ready`'s messages cannot be attributed to inputs. Getting them needs raft's trace hooks, which
  decision 2 rules out. (b) is also the binding's most intricate part: `Mem`, `Flush` with `more`
  (the merged undo, B 412-421), `Net`, `Made`, and batched sends checked against `mine`/`cast`/`dur`.
- (a)'s reports come from the `Ready` alone (`SoftState`, `HardState`, `Entries`, `Messages`,
  `CommittedEntries`), and `RawNode.Ready.spec` exposes exactly those (`hsOptC rd.HardState' h`,
  `role := roleAfter rs.role ss`, the entries `es`, the messages `ms` with `isRaftMsg`, the committed
  entries `ce`). The binding part it exercises is `Boot`, `Recv`, `Ready` (= `InMemory` + `OnDisk`
  with no batch), unbatched `Send`, `ApplyEv` and `GC`.
- `RawNode`'s specs are as complete as the node API's for running a node: all eighteen `RawNode`
  methods (`Step`, `Tick`, `Campaign`, `Propose`, `ProposeConfChange`, `Ready`, `readyWithoutAccept`,
  `acceptReady`, `HasReady`, `Advance`, `ApplyConfChange`, `ReadIndex`, `BasicStatus`,
  `ForgetLeader`, `TransferLeader`, `ReportSnapshot`, `ReportUnreachable`, `Bootstrap`) and
  `NewRawNode` are proved, no `sorry` or axiom in their proof files, and `Ready`'s spec carries the
  same durability *enter* as the node API's `readyEnter` (2026-11-01, stage II (k)).

Costs of (a), which are raft-side work:
- **Construction**: `NewRawNode.spec` returns the node *open* (`rawNodeFresh`); `ownRawNode` (with the
  cluster's ghost allocation) is established only inside `StartNode`'s and `RestartNode`'s proofs.
  A `RawNode`-level constructor law has to be factored out of them (no new reasoning expected).
- **Restart and crash**: restarting from a non-empty storage is specified only by `RestartNode`, and
  the real-crash law of #22 (`nodeVacant`, `nodeVacant_arm`, `nodeCrash`) only for
  `StartNode`/`RestartNode`/`node.Stop`. A harness that restarts nodes (in-process: drop the
  `RawNode`, `NewRawNode` on the same storage, `boot` report) needs a `RawNode` analogue (retire a
  generation without `Stop`). Recommendation: S2's first harness has no restarts; add them once the
  `RawNode` laws exist (§7 Q2).
- The trace check's harness proofs (`Cluster`, `RunConcurrent`) are over the node API; S2 reuses
  their shape (network bags, the recorder, bounded run), not their proofs of `node`.

## 7. S1: the Go checker (done)

`examples/raft/antithesis/check` (own `go.mod`, no dependencies): `types.go` (values), `raft.go`
(the `EtcdRaft.tla` operators the binding uses), `state.go` (variables, `Init0`), `binding.go` (every
operator and action of `EtcdBinding.tla`, each citing its lines), `check.go` (`Checker.Next`, `Run`:
GC when due, then `Step`; invariants on each new state), `verdict.go` (`Check`: `Run` with
evaluation errors as ERROR; `!goose`), `ndjson/` (the stream reader, as `TraceKit.java`), `cmd/
antcheck` (CLI: `antcheck [-cfg EtcdBinding.cfg] stream.ndjson`, prints streamcheck.py's line).
The model's `commits`, `applied` and `read` are left out: the binding never changes them and
nothing it evaluates reads them. Go subset of `tracecheck/etcdraft`: slices, structs, strings,
integers, panics; no maps, closures, generics, `fmt`, `sort` or `strings` outside `!goose` files.
The pinned Goose (Perennial `9c3b81f3`) translates the package without error or stub (13k lines).

**Differential test** (`go test`, no Java; fixtures from `testdata/gen-fixtures.sh` and
`testdata/gen-fuzz.py`, which run TLC through their `streamcheck.py`): verdict kind, event index and
violated properties must equal TLC's. Results in `notes/STATUS.md`'s entry of 2026-11-23 and the
branch's report; at this writing all agree (recorded traces 14/14, mutations 60/60 at TLC's index,
simulator streams 144/144 in twelve modes, plus a larger uncommitted batch and random
perturbations).

A self-mutation check of the transcription (flip one guard, rerun the test) caught 13 of 23
mutants with the traces, mutations and simulator streams alone; the survivors were guards no honest
stream fails (GC's trigger, `Boot`'s `~u.made`, `Net`'s `low`, `ApplyBeyondCommit`, ...). The random
perturbations (`gen-fuzz.py`) are there to reach those guards.

## 8. Questions for the user

**Q1. Initial state.** (a) `EtcdBindingEmpty.cfg`: empty logs, voters from the storage's
`ConfState` (needs `NewRawNode` on such a storage, risk 1); (b) `EtcdBinding.cfg`: the harness writes
`rawnode`'s boot entry (index 1, term 1, data `"boot"`) and `HardState{Term: 1}` into the storage
before `NewRawNode` (needs `NewRawNode`/restart on a non-empty storage at the `RawNode` level);
(c) `RawNode.Bootstrap` (rejected by both initial states). Recommend (a).

**Q2. Restarts.** (a) none in the first harness (every `boot` at start); (b) in-process restarts from
the start, which needs the `RawNode` restart and generation laws (§6); (c) real process crashes
(`Robust` with crashing machines, durable storage). Recommend (a), then (b) as a follow-up stage;
(c) adds nothing to the report shapes.

**Q3. Features in the first harness.** Proposals (with forwarding: `RestartNode.spec`'s premise
`DisableProposalForwarding = false` suggests keeping it on; the binding accepts `prop` sends),
elections, heartbeats; no snapshots/compaction, membership changes or read index (risks 5-8).
Recommend exactly that; read index next (cheapest: `ReadGiven` only checks the index).

**Q4. The checker's fidelity outside honest streams.** Where TLC stops with an evaluation error the
Go checker panics (`Run`) or says ERROR (`Check`); on a node name outside `Server` it errors where TLC
might reject. Both only matter for malformed streams, and either outcome makes `Main` panic.
Recommend accepting this.

**Q5. API.** (a) `RawNode` (recommended, §6) or (b) the node API.
