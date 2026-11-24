# Antithesis S4: the harness's proof and the closed theorem — statements (#33 S3c/S4)

Stage S4 of mit-pdos/etcd-grove#33, with S3c's remaining steps (2026-11-23; branch `antithesis-s4`,
from `antithesis-check` with `antithesis-rawnode-spec` merged). Phase 1 of the spec-first plan: every
statement, for review, before proofs. Builds on `notes/antithesis-check-design.md` (§1 the sketch of
the statement, §9 the harness, §10 the checker's spec) and `notes/antithesis-rawnode-design.md` (the
RawNode API, `InputEnd`, `ReadyOut`, the refinement `AntSim`). Where this note and those differ, this
note is the later decision and says why.

## 1. The closed statements

`antithesisProgram := antithesis.initialize' #() ;; (@! antithesis.Main) #()` and `antGF` (the
functors of tracecheck's `tcGF`, the same eight slots) in
`Proof/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/TopLevelDefs.lean`.

```lean
/-- The Antithesis check never fails: every real execution of `antithesisProgram` (the package's
initialization, then `Main()`: a three-voter cluster of the verified raft's `RawNode`s run
concurrently, `RunCluster(DefaultConfig())`, its stream of Antithesis default-mode reports checked
with `check.Run` against `EtcdBinding.tla` + `EtcdRaft.tla` at `EtcdBindingEmpty.cfg`'s constants,
and a panic unless ACCEPTED; proposal forwarding disabled, §7), from a fresh state with one thread, of `n` steps, `n + 4 ≤ 2^61`, along
which fewer than `2^31` threads are live at once, has no stuck thread and no thread that ended in
a panic; if the main thread has finished, its result is `#()`. -/
theorem raft_antithesis_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n + 4 ≤ 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow (2 ^ 31) n ([antithesisProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)

/-- As a robustness statement (`Robustness/Statement.lean`): the program alone on one machine that
never crashes, a fresh Go process. -/
def raft_antithesis_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
    (σ : state) (g : GlobalState),
    Robustness.Robust [] [(antithesisProgram, σ)] g (threads := 2 ^ 31) (bound := 2 ^ 61 - 3)
```

Differences from `raft_tracecheck_safe`, each because the program is different: **no premises**
(`tracecheck.premises boot`, `BootLogFacts` were the bootstrap log's `proto.Marshal` contract; the
harness's logs start empty and nothing is marshalled), **no `log.NewModel`** (the harness's logger
is its own `quietLogger`). The bounds are tracecheck's: `n + 4 ≤ 2^61` gives `receiptBound + 3 ≤ 2^61`,
which bounds the stream (`Stream.Bounded`: `1 + 2|evs| + Σ size < 2^61`, every report costing at least
`2 + size` receipts) and every reported number (terms through raft's term budget, indices through
the log's length).

**The corollary** (`raft_antithesis_accepts`, `Results.lean`), the program-level statement of what the
harness proves, at any `Config` of three nodes:

```lean
theorem raft_antithesis_accepts [ThreadBoundLe GF (2 ^ 31)] (Hrb : receiptBound GF + 3 ≤ 2 ^ 61)
    (cfg : antithesis.Config.t) (H3 : cfg.Nodes' = W64 3) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis }}
      (@! antithesis.RunCluster) #cfg
    {{ (c : Loc), RET #c;
        WP (c @!! go.GoType.PointerType antithesis.Cluster.ty @!! go!"Events") #()
          {{ v, ∃ (sl : GoSlice) (evs : List AntCheck.Event), ⌜v = #sl⌝ ∗ AntCheck.eventsRO sl evs ∗
                ⌜AntCheck.Accepts AntSim.cfg3 evs ∧ Stream.Bounded evs⌝ }} }}
```

`AntSim.cfg3 = { server := names 3, initVoters := names 3, bootstrapped := false }` (`names` the
Lean of the harness's `names`: `["raft1", "raft2", "raft3"]` as `GoString`s, ordered as `check.SetOf`
orders them). This is what the trace check's `raft_tracecheck_accepts` is to its program; the closed
theorem uses its proof, not its statement (`Main` also needs `c.Servers()`).

## 2. The harness's specs (one `Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/<fn>.lean` each)

Vocabulary, `Proof/.../antithesis/HarnessDefs.lean` (§3). Leaves:

| function | spec (sketch) |
|---|---|
| `below n` | `0 < n` → returns some `r < n` (tracecheck's) |
| `Name id` | `Name.spec`: returns `nameOf id` (`""` for 0, `"raft" ++ decimal`) |
| `names n` | returns a slice holding `namesL n` (`strsRO`-shaped, owned) |
| `entryOf e` | an entry `e` (`entPtsRO`) of type normal: returns `check.Entry` value `entOfRO v (entOf e)`; panics (out of scope) otherwise, so the spec's premise is `e.Type' = EntryNormal` |
| `entriesOf es` | all normal: a fresh slice of `entOf` of each |
| `msgType t` | returns `msgTypeStr t` (total, the switch) |
| `msgOf m to` | a message `msgIn ml □ st`, not a snapshot: returns the `check.Msg` value of `msgOfSt st to` |
| `roleOf s` | `roleStr s` |
| `bootStorage.*` | the six `raft.Storage` methods over a `MemoryStorage` of the harness's own, `InitialState` with `ConfState{Voters}` while no snapshot: the specs the interface's `Storage` contract (`StorageModel`) asks, as `KvrStorageApi.lean` proves kvreconf's wrapper |
| `DefaultConfig` | returns the constant record, `Nodes' = 3` |
| `Recorder.record ev` | `isRecorder γr r ∗ eventRO p ev ∗ AU <{ ∃∃ evs, recAuth γr evs }> @ ⊤, ∅ <{ recAuth γr (evs ++ [ev]), COMM Q }>` ⇒ `Q` (tracecheck's `SyncRecorder.TraceEvent`) |
| `Recorder.Events` | `isRecorder γr r ∗ recDone γr evs` ⇒ a fresh slice with `eventsRO sl evs` |
| `Cluster.node id`, `isolatedNow`, `isolate`, `Servers` | the obvious, over `isCluster` |
| `Cluster.deliver n inp` | `isCluster c γ ∗ inputOk γ n inp` ⇒ `()`: the input sent on `n.in` or dropped at `stop` |
| `Cluster.send m` | `isCluster c γ ∗ sentMsg γ ml st` (owned message, its persistent facts) ⇒ `()` (a goroutine is forked, joined through `netWg`) |
| `Cluster.reportCause n` | `nodeOwn c γ n D` with `D.cause = some m` ⇒ `recv` recorded (`antSim_recv`), `D.cause = none`; with none, nothing |
| `Cluster.drain n by` | `nodeOwn c γ n D` at an input's end (`D.phase = .input ps₀ ps₁ cause`) ⇒ `nodeOwn c γ n D'` between inputs, every `Ready` reported (§3) |
| `Cluster.run n` | `isCluster c γ ∗ nodeOwn c γ n D` (between inputs) ⇒ `nodesWg` done token |
| `RunCluster cfg` | `cfg.Nodes' = 3` ⇒ `runOver c` (below) |
| `Cluster.Events` | `runOver c` ⇒ the corollary's post |
| `Main` | `isPkgInit antithesis` ⇒ `()` (no panic) |

`runOver c := ∃ γ evs, isCluster c γ ∗ recDone γ.rec evs ∗ ⌜AntCheck.Accepts cfg3 evs ∧
Stream.Bounded evs⌝` (`recDone`: the recorder's events, no more report possible: every goroutine
that records has finished, `nodesWg.Wait()` and `netWg.Wait()` returned).

## 3. The harness's invariant (`HarnessDefs.lean`)

**Ghost names** `γ : AntNames`: raft's `Cluster` (the three nodes' `RaftNames`, the term budget), the
recorder `γ.rec` (an auth list of events), the views `γ.view` (an auth map `Fin 3 → NodeView`, the
node goroutine holding its fragment), and the sent messages `γ.sent` (a monotone set of `Msg`,
persistent witnesses `sentW γ m`).

**The global invariant** `antInv γ` (one Iris invariant, `antN`):

```lean
antInv γ := ∃ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin 3 → NodeView) (net : List Msg),
  recAuthHalf γ.rec evs ∗ viewAuth γ.view V ∗ sentAuth γ.sent net ∗
  ⌜AntSim.Prefix cfg3 evs S ∧ AntSim S V net ∧ Stream.Bounded evs⌝ ∗
  globalFacts γ S       -- C5's persistent raft facts for everything in S (§3.4 of the rawnode note)
```

`AntSim.Prefix cfg evs S := ∃ c, ((init0 cfg).bind fun s => evs.foldlM Checker.next {state := s})
= .ok c ∧ c.done = false ∧ c.state = S` — the checker has taken every event, rejected none, found
no violation; `Prefix → Accepts` (`Checker.finish` of a `done = false` checker is ACCEPTED).

**A report** is one `Recorder.record` whose AU the node goroutine discharges: it opens `antInv`,
reads `V n` (its fragment agrees), applies `antSim_gc*` then the report's lemma (`antSim_boot`,
`_recv`, `_ready`, `_send`, `_apply`) to get `S'`, `V'`, `net'` with `Prefix cfg3 (evs ++ [ev]) S'`,
updates the views and `sent`, records new facts (`globalFacts γ S'` from `globalFacts γ S` and the
report's raft facts), and commits `recAuth (evs ++ [ev])`. Pure lemma, one per report kind
(`Proof/.../antithesis/Sim/*.lean`):

```lean
def antSim_<kind>.stmt : Prop := ∀ S V net evs ev ...,
  Prefix cfg3 evs S → AntSim S V net → GlobalOk S ... → <raft's facts for this report> →
  ev = <the report, as a function of the raft data> →
  ∃ S' V' net', Prefix cfg3 (evs ++ [ev]) S' ∧ AntSim S' V' net' ∧ <V' n, net' as the report says>
```

(The GC the checker takes before each event is inside `Prefix`'s step: `antSim_gc`, used by each.)
No report changes another node's view (C1-C2 are per node; C3-C5 are about `S` and are kept).

**The node's own state** `nodeOwn c γ n D` (the goroutine's; `D : NodeData` the Go fields and the
phase): the `RawNode` (`rawNode γ.raft rn id rs ps qs`), its `MemoryStorage` (owned), the Go fields
`role term vote commit applied cause` (owned points-tos) agreeing with the view (`term vote commit`
the last `ready`'s, which the binding's `currentTerm` etc. are: C1), its view fragment, and the phase:
- *between inputs*: `qs = []`, `V n = (rs, ps)`, `PIdle` not needed (a fresh `HasReady` call decides);
- *after an input, before its first report*: `V n = (rs, ps₀)`, the node at `ps₁` with
  `InputEnd ps₀ ps₁` (`RecvEnd`/`TickEnd`/`ProposeEnd`) and the cause (the message, for `recv`);
- *in a drain, after a `Ready`*: the view at the `Ready`'s state (`ps` with the outbox emptied, the
  queue `qs`, the messages not yet reported `pend`), the `ready` report made or not needed;
- *after `Advance`*: `AdvanceEnd ps qs ps'`, as "after an input" with `ps₀` the view's.

**The network**: each in-flight message's goroutine owns the message (`msgPtsCC`), `sentW γ m`, and
the facts `RawNode.Step`'s premise needs (`isMessage`, `rnTermLB γ m.term` for the term ceiling).
`n.in`'s channel invariant: every queued input is `inputOk` (a message with those facts, or a
proposal's data, owned). The isolator and `isolated` (`isoMu`): no facts (it only drops).

**Termination of the run** (`RunCluster`'s end): `close(c.stop)`, `nodesWg.Wait()`, `netWg.Wait()`:
each node goroutine and each network goroutine gives back a token; with all of them `antInv`'s
`recAuthHalf` and the harness's other half give `recDone γ.rec evs` with `Prefix cfg3 evs S`, hence
`Accepts cfg3 evs`. (A node goroutine's last act is to drop its `rawNode`; no report after.)

## 4. What S3c still has to state (raft side; `notes/antithesis-rawnode-design.md` §2)

Unchanged from the reviewed design, steps 1b, 3, 4: the `nc` no-snapshot flag (§2.5's option (b)),
`ownRawNodeAt` with `qs` and the scope conjunct, the absSpecs of `Step`, `Tick`, `Propose`, `HasReady`
(`PIdle`), `Ready` (`ReadyOut`), `Advance` (`AdvanceEnd`), `NewRawNode.emptyStartSpec` (`pInit`),
the API module `RawNodeApi.lean` (`rawNode`, the laws, the budget re-exports). Two additions the
harness needs that the rawnode design did not list:
- **`NewRawNode` over the harness's `bootStorage`**: `emptyStartSpec` is over a `Storage` given by its
  specs; `bootStorage`'s six methods are proved to meet them (`bootStorage.*` specs, §2), from
  `MemoryStorage`'s (`MemstorageApi`).
- **`Ready`'s messages and entries as the harness reads them**: the harness calls `GetType`,
  `GetData`, `GetIndex`, `GetTerm`, `GetFrom`, `GetTo`, ... on the `Ready`'s `*pb.Message`s and
  `*pb.Entry`s and `proto.Clone`s each message before handing it to the network; `ReadyOut`'s `ms`
  carry `msgIn`-points-tos (read-only) and their records `st`, whose abstraction `absMsgOf st` is the
  protocol message in the outbox. `proto.Clone`'s spec (main tree `ClonePb`) gives an owned copy at
  the same record, which `RawNode.Step` takes.

## 5. The work list (after the review)

Each group writes its files only; shared vocabulary is fixed first (S-step) and not edited by a group.

| group | files | waits for |
|---|---|---|
| S-raft (statements) | `Proof/go_etcd_io/raft/v3/RawNodeAt.lean`, `RawNodeAbsSpecs.lean`, `RawNodeApi.lean` (statements, `def … .spec : Prop` and law statements) | — |
| S-sim (statements) | `Proof/.../antithesis/Sim/Abs.lean` (abstractions, the reports as functions), `Sim/Rel.lean` (`NodeView`, `AntSim`, `GlobalOk`, `Prefix`), `Sim/Stmts.lean` (the per-report lemma statements) | — |
| S-harness (statements) | `HarnessDefs.lean`, one spec file per harness function, `TopLevelDefs.lean`, `Spec/.../TopLevelRobustness.lean` | S-raft, S-sim names |
| P-raft-1b | the `nc` flag (raft step proofs: `maybeSendAppend` .. `raft.Step`) | S-raft; one big rebuild, alone |
| P-raft-3 | the absSpec proofs (`RawNode__*.lean`'s `wp_absProof`) | P-raft-1b for the no-snapshot facts |
| P-raft-4 | `RawNodeApiLinked.lean`, the laws' proofs | P-raft-3 |
| P-sim | the per-report lemmas (pure; independent of raft's proofs) | S-sim |
| P-harness | the harness's proofs, `Main`, adequacy, `Results.lean`, `TopLevelRobustness.lean` | S-harness |

Builds: one helper building at a time (the machine is CPU-starved); only cones to `.olean` locally;
full builds and gates through the VM land queue.

## 6. Status (2026-11-23, end of the first S4 session)

- **Approved** (the coordinator, 2026-11-23): §1's `raft_antithesis_safe`, `raft_antithesis_robust.spec`,
  `raft_antithesis_accepts` at `Nodes = 3`, `antGF` = `tcGF`'s slots. `TopLevelDefs.lean` and
  `Spec/.../antithesis/TopLevelRobustness.lean` are written and typecheck.
- **S-raft statements** (`RawNodeAt`, `RawNodeAbsSpecs`, `RawNodeApi`): written, typecheck; deviations in
  `notes/antithesis-rawnode-design.md` §2.6.
- **S-sim statements** (`Sim/Abs`, `Rel`, `Stmts`, `Smoke`): written, typecheck; `Prefix.accepts` proved; a
  51-report honest smoke stream built from `Abs`'s reports is accepted (`decide +kernel`); deviations in
  the rawnode note §3.5.
- **S-harness statements** (first part, typecheck): `Proof/.../antithesis/Base.lean` (the package's
  `IsPkgInit`, `True`: no package variable), `HarnessDefs.lean` (the pure readings `msgTypeStr`, `roleStr`,
  `entOfE`, `msgOfSt`; `CfgOk`, `defaultCfg`; `Stream.Fits`, `antRunFits`; `recAuth`/`recDone`,
  `isRecorder`; `runOver`; `bootStorRec`, `bootConfState`; `clusterRO`, `nodeOf`; `Pos.Countable` for the
  stream's types), and the specs of `below`, `Name`, `names`, `entryOf`, `entriesOf`, `msgType`, `msgOf`,
  `roleOf`, `DefaultConfig`, `Recorder.record`/`Events`, `Cluster.node`/`isolatedNow`/`isolate`/`Servers`/
  `Events`, `RunCluster`, `Main`, the six `bootStorage` methods. Deviations from §1-§2:
  * `RunCluster` takes `CfgOk cfg`, not only `Nodes = 3`: `time.NewTicker(c.cfg.Tick)` panics at a tick
    `≤ 0` (each node's `run`), and at `MaxDelay = -1` `send`'s `below(uint64(MaxDelay) + 1)` is `below(0)`,
    a division by zero, at the first message. `raft_antithesis_accepts` at any `cfg` with `Nodes = 3` is
    false as stated; it needs `CfgOk` (`DefaultConfig` meets it).
  * `Cluster.Events`' post (and `runOver`) has `Stream.ConfBounded cfg3 evs` beside `Accepts ∧ Bounded`:
    `check.Run` takes it, and it does not follow from acceptance (a stream with a conf entry may be accepted).
  * `runOver` is the recorder, `recDone` and `Nodes = 3` with the facts, not `isCluster` (which `Events`,
    `Servers` and `Main` do not need); the recorder's receipts are `⧗ (Σ Event.weight)` in its lock,
    `record` takes `⧗ ev.weight` from its caller (the caller's steps: `entriesOf`, `names` loop per entry),
    and its atomic update receives `Stream.Fits` at the commit; `quietLogger` gets no spec (raft's
    `isLogger` covers the four formatting methods only, which return `()` trivially; `Fatal*`/`Panic*` need
    none: raft's proof shows them unreachable).
- **S-harness, missing** (waiting on the open items and on the view's ghost state):
  * `antInv`, `isCluster`, `nodeOwn` with its phases, `inputOk`, `sentMsg`, the net join (the three nodes
    and `RunCluster` each `Add` to `netWg`: tracecheck's `NetJoin` shape, not importable from `RaftTla/`),
    and the specs over them: `Cluster.deliver`, `send`, `reportCause`, `drain`, `run`. The view ghost state
    (`γ.view`, a ghost variable of `AntSim.NodeView`) needs `Pos.Countable NodeView` (so `PState`, the
    protocol `Msg`, `Role`, `RdState`, ... countable), not yet written.
  * **`reportCause` after `Step` reads a message the harness no longer owns.** `run` does `n.cause =
    inp.msg; n.rn.Step(inp.msg); c.drain(n, "recv")`, and `drain`'s first report calls `reportCause`, which
    reads `n.cause` through its getters (`msgOf`). `RawNode.Step`'s precondition consumes the message
    (`msgPtsCC ml (DFrac.own 1) …`, not returned), and raft does write it (a follower's forward sets
    `m.To`, `stepFollower`; moot with forwarding off). So `run`'s proof cannot establish `reportCause`'s
    premise. Fix in the Go (recommended): compute the report before `Step` (`n.cause` a `*check.Msg` of
    `msgOf(inp.msg, n.id)`), or `Step` a `proto.Clone`; either needs a re-translation.
  * `Cluster.run`/`deliver`'s input invariant is to be stated without forwarding (open item 1), and
    `drain`'s `ready` report waits for the `ip` boundary (open item 2).
- **Open items for the coordinator:**
  1. *A forwarded `MsgProp`* at a leader is outside `raft.Step.spec`'s premise (`From = 0 ∨ From = id`) and
     `NetMsgOk`; `ProposeEnd`'s forward arm has the wrong `src` for a twice-forwarded proposal. Options: (a)
     widen `raft.Step`/`RawNode.Step` for a network `MsgProp` with the proposal resources (raft step cone
     rebuild); (b) `DisableProposalForwarding: true` in the harness (the binding checks nothing of `prop`).
     Recommended (b); asked.
  2. *`Ready`'s first entry.* The binding needs the first reported entry to be the first conflict with the
     durable log (B 378, 387). It is false as a post of `RawNode.Ready` in general (two inputs between
     `Ready`s can truncate and restore an entry; §2.6), true under the harness's discipline (each input from
     `PIdle`). The fix: `ownRawNodeAt` carries the in-progress boundary `ip` (`offsetInProgress - 1`), each
     input form's post says `ip' = min ip (common prefix of ps.log, ps'.log)`, `Ready` says `es ≠ [] →
     es[0].Index' = ip + 1` and resets `ip`. Touches every form; not yet done.
- **Stress evidence** (scratch, not committed): three extreme harness variants (split votes: 1ms ticks, 15ms
  delays, 20% loss; storm: 30 isolations of 8ms at 40% loss; burst: 200 proposals 0.2ms apart, 12ms
  delays), 340 runs each, every stream ACCEPTED by the Go checker. No discrepancy found.

## 7. Deviation: proposal forwarding disabled (the owner's decision, 2026-11-23) — to undo

**What.** The harness's `raft.Config` sets `DisableProposalForwarding: true` (`harness.go`, `RunCluster`,
with a comment pointing here): a follower drops a proposal (`ErrProposalDropped`) instead of forwarding it
to its leader. This reverses S2's decision Q3 (`notes/antithesis-check-design.md` §8-§9: forwarding on).
`raft_antithesis_safe` is about this configuration.

**Why.** With forwarding on, a leader steps a network `MsgProp` whose `From` is a follower, through
`RawNode.Step`. Raft's proved `raft.Step.spec` covers only local proposals (`From = 0 ∨ From = id`,
`Spec/go_etcd_io/raft/v3/raft__Step.lean:606`), and `NetMsgOk` excludes `MsgProp`: the node API never
needed more (its `node.Step` routes a network `MsgProp` to `propc`). `InputEnd.ProposeEnd`'s forward arm
also names the wrong source for a proposal forwarded twice (Go's `send` keeps a nonzero `From`). A spec
gap of our proof, not a raft bug or a discrepancy with the model.

**What the model check loses: essentially nothing.** The binding checks nothing of a `prop` send or
receipt (B 524, 586); a leader's append is checked by the same `Ready` guards whether it was caused by a
`recv` of a forwarded proposal or by a local `propose`. The runs differ only in which proposals reach a
leader (those handed to a follower are dropped), so fewer entries are committed per run.

**The future fix (option (a)), to re-enable forwarding:** widen `raft.Step.spec` and `RawNode.Step`'s
specs to a network `MsgProp` whose entries carry the proposal resources (the forwarded proposal's
tickets, `fwdP`), re-prove raft's `MsgProp` step paths (`stepLeader`'s, `stepFollower`'s forward) for
`From ≠ 0`, fix `ProposeEnd`'s forward arm (`src := if m.src = 0 then id else m.src`), and drop the
config line. Tracked by mit-pdos/etcd-grove#44.

**Re-run (2026-11-23), forwarding off:** S2's `TestRuns`, 5 variants x 100 runs, and the three stress
variants of §6 x 100 runs: 500 of 500 and 300 of 300 ACCEPTED by the Go checker (no `-race`).

**Revised (2026-11-24, S4 session 2): forwarding on in raft, forwarded proposals dropped by the network.**
`DisableProposalForwarding: true` contradicts raft's own proof: `ownRaftPhys` has the scope conjunct
`"%HpropForward" ∷ ⌜rv.disableProposalForwarding' = false⌝` (`InvRaftPhys.lean:1218`), `newRaft.spec` and
`NewRawNode.emptyStartForm` take `cv.DisableProposalForwarding' = false` as a premise, and `InputEnd.ProposeEnd`'s
follower arm is the forward. So the harness's `NewRawNode` call would be outside every proved spec, and
lifting it means recording the flag in the step cone's invariant (as `preVote` is) and a drop arm in
`stepFollower` and `ProposeEnd`: a full raft rebuild. Instead the harness keeps raft's default (forwarding on)
and `Cluster.send` drops every `MsgProp` (never delivered, so no leader steps a network proposal and no
proposal is forwarded twice). The stream gains `send` reports of `prop` messages, which the binding does not
check (B 524, 586) and `antSim_send` already covers; otherwise the runs are those of forwarding off. No raft
change; #44's fix (option (a)) then also removes the drop in `send`. Re-run: S2's `TestRuns`, 5 variants x
20 runs, 100 of 100 ACCEPTED (a default run has 9-20 `prop` sends).

## 8. Resume here (end of session 1, 2026-11-24)

Done: §1 approved and stated (`TopLevelDefs`, `Spec/.../TopLevelRobustness`); S-raft and S-sim statements
(typecheck); harness statements part 1 (`Base`, `HarnessDefs` leaves, 24 spec files: leaves, recorder,
`Cluster` accessors, `Events`, `RunCluster`, `Main`, `bootStorage`); forwarding off (§7, #44). Next, in order:
1. **Decisions to take** (coordinator): (i) `RunCluster`/`raft_antithesis_accepts` need `CfgOk cfg` (`Tick > 0`,
   `MaxDelay ≥ 0`, three nodes): with `Nodes = 3` alone the Go panics (`time.NewTicker`, `below(0)`); `Events`'
   post adds `Stream.ConfBounded`. (ii) The harness keeps `n.cause = inp.msg` across `RawNode.Step`, which
   consumes the message (`msgPtsCC … own 1`): change the harness to keep `msgOf(inp.msg, n.id)` (a `check.Msg`)
   as the cause before `Step` (behaviour-preserving: `msgOf` takes `to` as an argument and raft writes no
   field it reads once forwarding is off), then re-translate. (iii) The `ip` boundary in `ownRawNodeAt`
   (§6, open item 2).
2. Harness statements part 2: `Countable` for `NodeView` (ghost map), `antInv`, `isCluster`, `nodeOwn` and its
   phases, `inputOk`, `sentMsg`, specs of `deliver`, `send`, `reportCause`, `drain`, `run`.
3. Invariant phase: make `AntSim` (C1-C5, `Sim/Rel.lean`) inductive against `Sim/Stmts.lean`'s lemmas.
4. Parallel proofs (§5): P-sim (pure lemmas), P-raft-1b/3/4 (one big rebuild at a time), P-harness.
Builds: worktree `tmp/eg-ant4` has a seeded `.lake` (oleans hard-linked from `tmp/ant`, rest copied); helpers
use `flock /tmp/ant4-build.lock` and `etc/lean-check.py` (server class) rather than `lake build`.
