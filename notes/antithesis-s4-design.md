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
and a panic unless ACCEPTED), from a fresh state with one thread, of `n` steps, `n + 4 ≤ 2^61`, along
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
