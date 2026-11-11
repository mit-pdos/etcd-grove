# Trace-check: the design pass, from the closed theorem down to the proved pieces (2026-11-11)

The user approved this pass (2026-11-11) under `notes/spec-first-plan.md`'s *Design before plumbing*:
before more threading, the whole chain is written as text, each statement with what it is
proved from and why that suffices, for review. Nothing here is threaded or proved. Every Lean
statement below is a text sketch, **not typechecked** (no Lean was run). Old → new is given wherever
a statement exists today. Branch `trace-check-design`, from `trace-check` at `c2325abf53`.

Reading order: §1 is the only part the user reviews. §2-§6 are the agent's (intermediate statements,
recorded per "The gates, delegated"). §7 is the whole chain as one table. §8 is the probe to run after
review. §9 lists the links that are not argued and the decisions.

Vocabulary used throughout: `TrNetTy t` (`MsgApp`, `MsgAppResp`, `MsgVote`, `MsgVoteResp`,
`MsgHeartbeat`, `MsgHeartbeatResp`), `AckTy` (`MsgStorageAppendResp`, `MsgStorageApplyResp`),
`recvTokOf` (`TracedRecvTok.lean`), `trTok` (`TracedNodeApi.lean`), the capability `trCapB`
(`TracedCap.lean`), `rnTrace` (`InvRawnode.lean`).

---

## 1. The closed statements (THE USER REVIEWS ONLY THIS SECTION)

Both go in `Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Results.lean`. They replace
`raft_tracecheck_safe_of` (which takes `TcOpen`) once `RunConcurrent.spec` is proved.

### 1.1 The premise bundle (Q32, the user's decision, 2026-11-11)

Modelled on `etcd_putget.BootFacts` and `etcd_putget.premises` (`examples/etcd/putget/Defs.lean`).
New file `Proof/.../tracecheck/Defs.lean`:

```lean
/-- The bootstrap log `StartNode` builds for the peers `1, 2, 3` (each `Peer{ID: i}`, `Context`
nil), as Go computes it: three conf-change entries of term 1 whose data is the marshalled
`ConfChange{Type: AddNode, NodeID: i}` (the node API's `BootLog`). -/
abbrev tracecheck.BootFacts (boot : List LogEntry) : Prop :=
  BootLog [W64 1, W64 2, W64 3] [[], [], []] boot

/-- **`Main`'s named premise** (Q32): `proto.Marshal`'s contract at the bootstrap log's conf
changes. Each of the three `StartNode`s marshals `AddNode i`, and the call returns the bytes of
`boot`'s `i`-th entry (`bootMarshal`, persistent). Raft's proof needs the three voters' logs to be one
committed log. `proto.MarshalConfChange.spec` gives only bytes that decode to the change. -/
abbrev tracecheck.premises (boot : List LogEntry) : IProp GF :=
  bootMarshal [W64 1, W64 2, W64 3] [[], [], []] (LogEntry.toEntries boot 0)
```

No axiom changes (Q32: "follow the etcd examples"). The bundle holds `bootMarshal` only. It is a
named bundle so that a later premise could join it, but none is planned (§6: Q33 uses an existing
axiom, and Q34 and Q35 add no premise).

### 1.2 `raft_tracecheck_safe` (the closed theorem)

```lean
theorem raft_tracecheck_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [hLog : log.NewModel]
    (boot : List LogEntry) (Hbf : tracecheck.BootFacts boot)
    (Hprem : ∀ hG : HeapGS .hasLC tcGF,
      ⊢ tracecheck.premises (GF := tcGF) (hG := heapWith hG lctx) boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n + 4 ≤ 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([tracecheckProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

**What changes from `raft_tracecheck_safe_of`'s statement:** `hopen : TcOpen` is gone. Three
binders are added: `boot`, `Hbf` and `Hprem` (Q32). Everything else is word for word: the program,
the step bound `n + 4 ≤ 2^61` (S7 part 1), the three conclusions and the instance context.
`tracecheckProgram` is the package's initialization, then `Main()`; `Main` runs
`RunConcurrent(DefaultCConfig())`, `ConvertEvents`, `NewTrace`, and `CheckTrace(tr, true)`, and panics
unless `TLCOK`.

### 1.3 `raft_tracecheck_accepts` (the corollary: every run's trace satisfies `TraceAccepts`)

`TraceAccepts` is unchanged (`etcdraft/Tla/Check.lean`):
`TraceAccepts events pv cq := ∃ t, newTraceWith events pv cq = .ok t ∧ ∃ res, CheckTraceRel t true res ∧ res.tlcOK = true`.

```lean
theorem raft_tracecheck_accepts [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    (Hrb : receiptBound GF + 3 ≤ 2 ^ 61) (boot : List LogEntry) (Hbf : tracecheck.BootFacts boot) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
        context.isClosedchanInit ∗ tracecheck.premises boot }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent))
        (Val #defaultCConfig))
    {{ (c : Loc), RET (PairV #c #interface.nil);
        WP (App (Val (c @!! go.GoType.PointerType Cluster.ty @!! go!"Events")) (Val #()))
          {{ v, ∃ (sl : GoSlice) (L : List TraceEv), ⌜v = #sl⌝ ∗ traceEventsRep sl L ∗
                ⌜Etcdraft.TraceAccepts (L.map TraceSim.evConv) false false⌝ }} }}
```

It is the composition of `RunConcurrent.spec` (§2.1) with the existing, proved
`tracecheck_Events_traceAccepts`. It is stated at `defaultCConfig`, the value `DefaultCConfig()`
returns (its proved spec), so that the closed statement does not expose `Workload` (§2.1).
**New**: the corollary had no stated form before (`Results.lean` has only its core). The user
reviews this form. Alternatives:
- (b) quantify over `cfg` with `Workload cfg`: more general, but `Workload`'s definition then becomes
  part of the closed statement;
- (c) keep only the core and say in prose that `RunConcurrent.spec` composes with it: no closed
  corollary.

Recommended: the form above.

**Nothing else in the chain below is the user's.** The trust base is unchanged: no axiom is added.
§6 explains why `strconv.Itoa`'s existing axiom joins this collection's report without being a
trust-base change.

---

## 2. `RunConcurrent` and the harness: what each piece uses from the node API

### 2.1 The harness's own statements (layer D, the agent's)

- **`Workload`** (`Spec/.../tracecheck/RunConcurrent.lean`). Old: three voters, no extra node, no
  configuration change, no snapshot, `0 ≤ MaxDelay < 2^62`. **New** (Q35 (a)): add
  `0 < sint.Z cfg.Tick'`. `time.NewTicker` panics otherwise. `DefaultCConfig`'s 10ms meets it:
  `Main`'s proof gains one `decide`.
- **`RunConcurrent.spec`**. Old:
  `receiptBound GF + 3 ≤ 2^61 → ∀ cfg, Workload cfg → {{ isPkgInit ∗ context.isClosedchanInit }} RunConcurrent #cfg {{ c, RET (c, nil); runOver c }}`.
  **New**: add the binders `∀ boot, tracecheck.BootFacts boot →` and the conjunct
  `tracecheck.premises boot` in the precondition. `runOver c` is unchanged.
- **`Main.spec`**, `tcMainSpec`, `tracecheck_adequate_of`: the same binders, threaded. `Main` passes
  `premises boot` to `RunConcurrent`. The adequacy threads `Hprem` exactly as `etcd_putget_adequate`
  does (`ihave #Hprem' := Hprem hG`).
- **`TcOpen`** is deleted once `RunConcurrent.wp_proof` exists. `Results.lean` then states §1.

### 2.2 `RunConcurrent`'s body (`concurrent.go`), call by call

| Go | Statement used | Old → new | What the proof needs from it |
|---|---|---|---|
| `&Cluster{…}`, `&SyncRecorder{}`, `make(chan struct{})` | Goose allocation; the recorder's lock (`isSyncRecorder`, S7 part 1) | unchanged | the trace's two halves: `traceFrag γt []` to the names, `traceAuth` under the lock |
| (ghost) | `harness_alloc` (`HarnessAlloc.lean`): `traceNames_alloc`, `cluster_alloc_traced`, `Cluster.traceSim_alloc` | `traceNames_alloc` also allocates `ghostMapAuth tn.dn 1 ∅` (A8.2) | the traced cluster `γ`, `traceDir γd tn`, `Cluster.traceSim γ vs tn`, each voter's `voterStart` |
| `raft.NewMemoryStorage()`, `&raft.Config{…}` | the storage contract (`restartStorage`, as kvreconf) | unchanged | `ConfigValid`, `TraceLogger ≠ nil` (`c.rec`), `MaxSizePerMsg = ^0`, `AsyncStorageWrites = false` |
| `raft.StartNode(rc, peers)` ×3 | `StartNode.tracedSpec` (`TracedNodeApi.lean`) | **`D` fixed to `bootDone`** (A8.3): the post's `startDone γ D cv.ID'` becomes `startDone γ cv.ID'` = `∃ tn, traceDir γd tn ∗ bootDone tn cv.ID'` | `isNode`, `nodeDriver … init`, `nodeConfig`, `nodeRunning 1`, the persistent `bootDone` |
| `c.apps.Add(1); go c.app(r)` ×3 | `sync.join` (`WaitGroupJoin`: three `Add(1)`s, `num_added ≤ 3`) | unchanged | each `app` gets `nodeRunning 1`, `isNode`, the driver state, a third of the network's adder right (§6, Q34), and `ownDone apps P'` with `P' := nodeRunning 1 ∗ njAdder ⅓` |
| `drivers.Add(3)` | a local `join3` lemma over the raw `WaitGroup.Add` spec (three `ownDone`s from one `Add(3)`; `join` has `Add(1)` only) | new (harness-local, glue) | three driver goroutines |
| isolation driver | `time.Sleep`, `atomic.Uint64.Store`, `below` (proved) | unchanged | nothing of raft |
| proposer | `below`, `context.WithTimeout`, **`strconv.Itoa`** (existing axiom, §6 Q33), `node.Propose.spec` (unchanged), `cancel`, `atomic.Int64.Add`, `time.Sleep` | unchanged | `Propose` puts one **normal** entry on `propc` (`propP`'s first disjunct), which the traced `propc` arm needs (`PropAny`) |
| conf-change proposer | `atomic.Int64.Load` of `ConfChanges` at a persistent `0` (`Workload`'s `ConfChanges' = 0`: the loop's `&&` short-circuits, so `time.Now` and `Status` are never called) | unchanged | the counter is never written; its points-to is made persistent at allocation |
| `drivers.Wait`, `time.Sleep`, `close(c.stop)` | `join3`, `time.Sleep`, the channel close | unchanged | — |
| `c.apps.Wait()` | `sync.join.WaitGroup.wp_Wait` | unchanged | the three `nodeRunning 1` and the three `njAdder ⅓` back |
| `r.node.Stop()` ×3 | `node.Stop.spec` | unchanged | `nodeRunning 1` in |
| `c.net.Wait()` | `netJoin` (§6, Q34): `njClose` (`njAdder 1` → the wait token), then the raw `Wait` | new (harness-local) | the counter reaches 0 (every network goroutine `Done`) |
| `return c, nil` | `runOver_intro` (`HarnessEnd.lean`) with **`BootEnd`** discharged by `Cluster.traceSim_bootEnd` (A8.4) | `BootEnd D` becomes a theorem at `D := bootDone` (it was a hypothesis) | `□ [∗list] i ∈ vs, bootDone tn i` (from the three `StartNode`s), `nodeBoot`, `Cluster.traceSim` |

### 2.3 `app` (one per replica)

| Go | Statement used | Old → new |
|---|---|---|
| `time.NewTicker(c.cfg.Tick)`, `defer ticker.Stop()` | Perennial's `time.NewTicker.spec` (needs `0 < Tick`: Q35) | unchanged |
| `case <-c.stop: return` | the closed-channel receive; `apps.Done` with `nodeRunning 1 ∗ njAdder ⅓` | unchanged |
| `case <-ticker.C: r.node.Tick()` | `node.Tick.spec` (`isNode` only) | unchanged: its traced content is `run`'s `tickc` arm |
| `case rd := <-r.node.Ready()` | `isReadyChan_recvAu.tracedSpec` | **changed** (29n finding 4): `readyGotT`'s last conjunct is the claim `readyToksClaim n γ N ms`, no longer the tokens `[∗list] q ∈ ms, trTok γ q.st` (§3.1) |
| `c.handleReady(r, rd)` | `raft.IsEmptySnap`, `MemoryStorage.Append`/`SetHardState` (storage contract), `proto.Unmarshal`, **`node.ApplyConfChange.spec`** (the three bootstrap conf entries, with the decisions authority, as kvreconf's `confPolicy`), `atomic.Int64.Add` | unchanged. The snapshot branches are dead: `IsEmptySnap` holds (`TrNoSnap`), and `SnapshotEvery = 0` |
| `r.node.Advance()` | **`node.Advance.tracedSpec`** (new, §3.1) | the claim in, `[∗list] q ∈ ms, trTok γ q.st` out. The stopped disjunct is refuted by `nodeRunning_stopped`: the `app` holds `nodeRunning 1` |
| `for _, m := range rd.Messages { c.send(r, proto.Clone(m), …) }` | `proto.Clone` (as kvreconf), `below`, `send` (below) | each `q ∈ ms` is sent with its `trTok γ q.st` |

**When the harness sends, checked against the Go.** `app` calls `handleReady`, then `Advance`, then
`send` for each message (`concurrent.go`, the comment at the loop). `node.Advance` returns only once
`run` has taken the `advancec` rendezvous (or is stopped). `run` arms `advancec` only in the `readyc`
arm, after `n.rn.acceptReady(rd)` has returned, and `acceptReady` ends with `traceReady`, the `Ready`
line that mints the tokens. So every message is handed to the network after its sender's `Ready`
line. The tokens are therefore available exactly when the harness needs them: at `Advance`'s return
(29n finding 4; Q3's F1).

### 2.4 `send` (one goroutine per message)

| Go | Statement used | Old → new |
|---|---|---|
| `c.net.Add(1)` (in `app`), `go func(){…}` | `netJoin.wp_Add` (§6, Q34): the caller's `njAdder ⅓` and its thread token in, `njDone` out | new (harness-local) |
| `time.Sleep`, `c.replica(m.GetTo())` (proved), `m.GetType()`, `m.GetTo()`, `isolated.Load` | Perennial, `Cluster.replica.wp_proof`, the message getters | unchanged |
| `dst.node.Step(ctx, m)` | **`node.Step.tracedSpec`** | statement text unchanged. `trTok`'s sealed body gains the message's type fact `TrSent` (§3.6) |
| `if typ == pb.MsgSnap` (twice) | the new law **`trTok_type`**, read before `Step` consumes the token: `trTok γ st ⊢ trTok γ st ∗ ⌜Cluster.trace γ ≠ none → st.msg.Type' ≠ MsgSnap⌝` | new law. Both `ReportSnapshot` calls are dead |
| `src.node.ReportUnreachable(to)` | `node.ReportUnreachable.spec` (`isNode` only; it may run after `src` is stopped: `<-n.done`) | unchanged: its traced content is `run`'s `recvc` arm on `UnreachPath` |
| `c.Dropped/Delivered.Add`, `cancel` | Perennial | unchanged |
| `defer c.net.Done()` | `netJoin.wp_Done` (the slot's thread token back) | new |

A dropped or timed-out message's token is discarded (the logic is affine). At most once holds
because the token is consumed by the one `Step` that delivers it.

---

## 3. The node API's traced statements, and the gated `node.run` that proves them

### 3.1 The client statements (`TracedNodeApi.lean`, on `etc/api/raft.txt`)

Design rule: each traced statement is gated, and its untraced instance is the current statement.
Untraced, `trTok` and `readyToksClaim` are `True` (`trTok_untraced`, new `readyToksClaim_untraced`).
So the current `node.X.spec` is derived from `node.X.tracedSpec` (one proof per function), and
no existing client changes. The exception is §3.5.

| Function | Old (today) | New |
|---|---|---|
| `StartNode` | `StartNode.gatedSpec` (frozen Draft, over `startTrace`); `StartNode.tracedSpec D` (hypothesis, `D` free) | A8.3: the gated post gains `startDone γ cv.ID'` (`bootDone`). `StartNode.tracedSpec` is no longer parametric. Proved from `setupNode`'s traced spec (§5) |
| `node.Tick` | `node.Tick.spec` (`isNode`) | unchanged |
| `node.Ready` / `isReadyChan_recvAu` | untraced law; `.tracedSpec` (hypothesis) with `readyGotT` = `readyGot` ∗ `[∗list] q ∈ ms, trTok γ q.st` (**unprovable**, 29n finding 4) | `readyGotT` = `readyGot` ∗ **`readyToksClaim n γ N ms`**. `.tracedSpec` becomes a theorem, and `isReadyChan_recvAu` is its untraced instance |
| `node.Advance` | `node.Advance.spec` (no tokens) | **`node.Advance.tracedSpec`** (new): `node.Advance.spec`'s pre ∗ `readyToksClaim n γ N ms`. Post: its first disjunct ∗ `[∗list] q ∈ ms, trTok γ q.st`; the stopped disjunct gives nothing. `node.Advance.spec` is the untraced instance |
| `node.Propose` | `node.Propose.spec` | unchanged (the `propc` payload's entry is normal by construction) |
| `node.ApplyConfChange` | `node.ApplyConfChange.spec` | unchanged (traced content: `run`'s `confc` arm) |
| `node.Step` | `node.Step.spec` (`stepIn`); `.tracedSpec` (hypothesis): stepIn's premises inlined ∗ `trTok γ st` | text unchanged. A theorem now. `trTok`'s sealed traced body becomes `⌜TrSent st⌝ ∗ recvTokOf γd …` (§3.6). New law `trTok_type` (§2.4) |
| `node.ReportUnreachable` | `node.ReportUnreachable.spec` | unchanged |
| `node.Stop` | `node.Stop.spec` | unchanged |
| `node.ReadIndex`, `.TransferLeadership`, `.ForgetLeader`, `.ReportSnapshot`, `.ProposeConfChange` | no trace premise | **refused at a traced node** (§3.5): each gains `Cluster.trace γ = none →` |

```lean
/-- The driver's claim on the tokens of a received `Ready`'s messages `ms` (sealed; exclusive).
Untraced `True`. Traced: the driver's half of the node's ghost variable recording the `Ready`'s
handed-out messages. -/
@[no_expose] def readyToksClaim (n : Loc) (γ : Cluster) (N : Namespace) (ms : List QMsg) : IProp GF

abbrev node.Advance.tracedSpec : Prop :=
  ∀ n γ N id st es L v (ms : List QMsg), st.handling = some (es, L) →
  (∀ l, L = some l → l.dlv.length = uint.nat l.snap.Metadata'.Index') →
  {{ isPkgInit pkg_id.go_etcd_io.raft.v3 ∗ isCluster γ N ∗ isNode n γ N id ∗ nodeDriver n γ N st ∗
      advReceipt st.storage st.delivered.length es L ∗ nodeConfig n γ N v ∗ (match L with …) ∗
      readyToksClaim n γ N ms }}
    n.Advance()
  {{ RET #(); (nodeDriver n γ N { st with handling := none } ∗ nodeAppliedLb γ st.key st.delivered.length ∗
        (match L with …) ∗ [∗list] q ∈ ms, trTok γ q.st) ∨
      (nodeStopped n γ N ∗ nodeDriver n γ N { st with handling := none }) }}
```

### 3.2 The gated `node.run`

**`node.run.spec`**. Old: `∀ γ id n, γ.raft.reTrace = none → {{ isPkgInit ∗ isNodeChan γ id n ∗ runPre γ id n }} n.run() {{ True }}`.
**New**: the premise `γ.raft.reTrace = none` is dropped, so there is one spec for both modes. Its
traced content is in the invariants it opens (below). Its `wp_proof` cites the callee specs it
cites today, plus `raft.Step.spec` with the proved `stepBundle_traced` (slice 30c, applied as
`stepBundle_traced.on_of_statement` / `onG_of_statement`), `raft.tickElection.spec`,
`raft.tickHeartbeat.spec`, and the traced RawNode triples of §3.3.

**What the node's invariants gain (sealed, raft-internal):**
1. **`ownRawNode`'s traced conjunct** (`rnTrace`, slice 25n) gains:
   - *(a) flag to delivery* (29n finding 2): `rs.delivered ≠ [] → b = true` for the capability's
     `∃ b`. `rnTrace` takes `rs` (or the clause sits next to it in `ownRawNode`).
   - *(b) the outbox's types* (§3.6, G1): `TrOutTy s` = `∀ m ∈ s.outbox, m.ty ∈ {app, appResp, vote,
     voteResp, heartbeat, heartbeatResp} ∨ (m.ty = propose ∧ its entries normal)`, together with the
     scope facts it needs: `s.lt = none` (no transfer target) and no pending read request (`ReadIdle s`).
2. **`readyP`** (the `readyc` payload): the driver's half of a new ghost variable `γ.rtk` at the
   `Ready`'s `ms` (the claim, gated on the trace mode). `run` keeps the other half.
3. **`run`'s loop invariant in the busy state** (after `acceptReady`, `advancec` armed; the
   `runMid_busy` of today): `[∗list] q ∈ ms, readyTok γ q.st` (acceptReady's `"Htoks"`) ∗ `run`'s half
   of `γ.rtk` at `ms`.
4. **`advInv`** (the `advancec` protocol). The tokens and `run`'s `rtk` half go where the driver
   collects them:
   - in `advDep` (`run` waits first, `RcvPending`): the sender takes the tokens at its commit, and the
     driver's half goes into `advRet`;
   - in the `RcvCommit` answer (the driver offered first, `SndPending`): `run` has both halves after
     the receive, and puts the tokens with the agreeing `req` half, extended to carry `ms`.
   Either way the claim and the deposit agree (`dghostVar` agreement), and `run` ends the rendezvous
   with both `rtk` halves, ready for the next `Ready`.
5. **`netP`** (the `recvc` payload), gated:
   - traced, a network message also carries `⌜TrNetTy st.msg.Type'⌝ ∗ recvTokOf γd st.msg st.ents st.ctx`;
   - the local disjunct is restricted to `MsgUnreachable` (`ReportUnreachable`), plus `hupP`
     (`Campaign`);
   - untraced, `True` and unrestricted.
6. **`fwdP`** (a forwarded proposal on `propc`), gated: `∀ e ∈ st.ents, e.Type' = EntryNormal`.

**Arm by arm** (the `select` in `node.go`'s `run`):

| Arm (Go) | Callee triple | Proved? | Premises from where |
|---|---|---|---|
| loop head: `n.rn.HasReady()`, `n.rn.readyWithoutAccept()` | `HasReady`, `readyWithoutAccept.spec` (one spec for both modes, slice 28n) | yes | `ownRawNode` |
| `case pm := <-propc: m.From = r.id; r.Step(m)` | `wp_rn_raft_Step_prop_traced` over `stepBundle_traced.onG PropAny` (from the assembly by `onG_of_statement`) | yes (25n, 30c) | `PropAny`: `MsgProp`, non-empty, **normal entries** (`propP`: `Propose`'s one normal entry; `fwdP`'s new gated clause), `γ.reBoot ≠ []` (the capability, `trCapB_reBoot`). The bounds from the ceiling (below) |
| `case m := <-recvc` (guard: response from an unknown `From` → drop; else `r.Step(m)`) | `raft.Step.traced` (`raft.Step.tracedTriple`, slice 30c) | yes | the token and `TrNetTy` from `netP` (5.); `StepNodeOk`'s `MsgAppResp` clause from the guard's `Progress` lookup (as `RawNode.Step.traced`'s third guard); `MsgUnreachable` at term 0 (`UnreachPath`); `MsgHup` from `hupP`. The rest: §4 |
| `case cc := <-confc: r.applyConfChange(cc)` | traced `raft.applyConfChange` → traced `switchToConfig` | **no** (29n items 1-2) | the capability **booted** by 1(a): `DynCCPre` puts the entry inside the delivered log, so `rs.delivered ≠ []`. `trCapB_hookGate_applyCC` (proved) at a non-leader; the leader case: §3.4 |
| `case <-tickc: n.rn.Tick()` | `RawNode.Tick.traced` (26n) | yes | `tickInv`'s credit; the bounds |
| `case readyc <- rd: n.rn.acceptReady(rd)` | `RawNode.acceptReady.spec` (one spec, slice 28n): fires the `Ready` line (`rnTrace_fireReady`), post `[∗list] q ∈ ms, readyTok γ q.st` | yes | `ownRawNodeReady` (with `MsSub`, `OutTr`); the gated bounds premise |
| `case <-advancec: n.rn.Advance(rd)` | traced `RawNode.Advance`: `stepsOnAdvance`'s self-addressed responses over `raft.Step.traced` with `pendingRel`'s `selfTok` (Q26 (a)); the storage acknowledgements over `stepBundle_traced_storAck` (`.onA`, `AckEnd`) | **no** (designed in 28n, `AckEnd` done in 30c) | the self tokens from `pendingRel`'s `.self` arm; `TrNoSnap` makes the snapshot arm vacuous. The handed-out tokens leave at the rendezvous (4.), before `RawNode.Advance` runs |
| `case c := <-status` | `getStatus` | yes (reads only) | — |
| `case <-stop: close(done)` | the stop protocol | yes | — |

**The bounds premises of the traced triples** (`uint.Z rs.tc + 1 < traceNumBound`, and
`receiptBound GF + γ.reBoot.length ≤ traceNumBound`):
- The first: `run` holds `termLB γ.bud rs.tc`. Opening `budgetInv` (`M ≤ k + 1` with `⧗ k`, so
  `k < receiptBound`) gives `rs.tc ≤ M ≤ receiptBound GF`, and `receiptBound GF + 3 ≤ 2^61` (the
  cluster's `readyFits`) gives the premise.
- The second is the cluster's `readyFits` itself (`γ.reBoot.length = 3`).

Both are read once per arm. No new invariant is needed.

### 3.3 The RawNode triples `run` uses

- **Proved:**
  - `RawNode.Tick.traced` (26n).
  - `raft.Step.traced` with the assembly (30c), and `wp_rn_raft_Step_prop_traced` (25n).
  - `RawNode.acceptReady.spec` and `RawNode.readyWithoutAccept.spec` (one spec each, 28n).
  - `stepBundle_traced_storAck` (30c) and `stepBundle_traced_unreach` (27n).
  - `trCapB_hookGate_applyCC` and `traceConfChangeEvent.tracedSpec_proof` (29n).
  - `RawNode.Step.traced`, `RawNode.Ready.traced` and `RawNode.ReportUnreachable.traced` exist but
    are **not on `run`'s path**: `run` calls `r.Step` and `acceptReady` directly. Their proofs are
    the models for the `recvc` arm.
- **Not yet:**
  - the traced `RawNode.Advance` (28n's design);
  - the traced `raft.applyConfChange`, `raft.switchToConfig` and `RawNode.ApplyConfChange` (29n items 1-2);
  - the traced `newRaft`, `NewRawNode`, `Bootstrap` and `setupNode` (§5).

### 3.4 `switchToConfig`: the read-only lending, the leader case

- **Read-only lending** (29n finding 1, recommended (a), taken here): `traceEvent.spec` takes
  `RaftReadLend` (the hard state's fields, `raftLog`'s `lastIndex`, `state`, `id`, the tracker's
  `Config.Voters` maps; no `Progress`) in place of `RaftLend`.
  - `raftLend_self` gives it from the whole struct, so every other hook caller changes only by that lemma.
  - The `Changer` specs (`Simple`, `EnterJoint`, `LeaveJoint`) give back the old configuration's maps,
    which are only read (`Config.Clone`).
  - `switchToConfig` lends them from its open struct.
  - `traceConfChangeEvent.spec` then becomes one spec for both modes over `RaftReadLend`. Its callers
    are `switchToConfig` and `newRaft`'s call (A7).
  - Argument: `traceEvent` reads exactly those fields (29n). The shallow `Progress` copies share the
    `Inflights` rings, but no ring is read.
- **The leader case** (29n finding 3). At a leader, `switchToConfig` also runs `maybeCommit` (a no-op
  `Commit` line) and `maybeSendAppend` per peer. Worse, `trCapB_hookGate_applyCC` needs `AccIdle`,
  whose clauses include *not a leader*, so the `ApplyConfChange` line at a leader has no line lemma at
  all. 29n recommended proving the leader case. **This pass recommends excluding it instead**, by an
  argument that needs no new line lemma:
  1. At a traced cluster every conf entry `run` applies via `confc` is a bootstrap entry. The
     refusal of `ProposeConfChange` (§3.5) and the normal-entry clauses (`propP`, `fwdP`) leave no
     other conf entry in any log.
  2. `raft.hup` refuses to campaign while `hasUnappliedConfChanges()`, and `Bootstrap` leaves
     `raftLog.applied = 0` with the `|C|` conf entries committed. So a node that is not a follower
     has `applied ≥ |γ.reBoot|`. `applied` is monotone. This is a new pure clause of `rnTrace`:
     `s.role ≠ follower → applied ≥ |γ.reBoot|`. It is established at `hup`'s campaign:
     `HupCampaigns` already carries `¬ hasUnappliedConfChanges`.
  3. At the `confc` arm the entry's index `k + 1` exceeds `raftLog.applied`. The driver applies
     conf entries before its `Advance`, and `run` checks A1 at `Advance` (`advanceP`'s `undecFree`
     at `cam`), so no `Advance` has gone past an unapplied conf entry.
  4. From 2 and 3, the node is a follower at the `confc` arm, so `AccIdle` applies.

  **Not checked in Lean**; flagged in §9 (L2). If step 3 does not follow from A1 as stated, the
  fallback is 29n's: a line lemma for `ApplyConfChange` at a leader under the corrected
  specification. That lemma is not argued here either.

### 3.5 The calls refused at a traced node

`run`'s `recvc` and `propc` arms can only step what the traced bundle covers (`StepEndTy ∨ AckTy`).
At a traced node the following arrive through those arms and are covered by no path:
- `MsgReadIndex` (`ReadIndex`);
- `MsgTransferLeader` (`TransferLeadership`);
- `MsgForgetLeader` (`ForgetLeader`);
- `MsgSnapStatus` (`ReportSnapshot`);
- a conf-change `MsgProp` (`ProposeConfChange`, a `ChangeConf` the workload excludes).

Each of these five `node.X.spec`s gains the premise `Cluster.trace γ = none`, and `netP`'s traced
local disjunct is restricted (§3.2, 5.). None is called by the harness. `ReportSnapshot`'s call is
dead by `trTok_type`. This is Q6's "refused calls" at the node level.
- **Cost**: every existing caller must supply the pure fact, which untraced clients have since Q6
  (the acceptance test allows `interface/` to differ by it). The etcd server's call sites
  (`raftNode`, the read loop's `ReadIndex`, `TransferLeadership`) must be counted with
  `etc/importers.py --uses` before threading.
- **Rejected**: bundle paths for these types. `MsgTransferLeader` leads to `MsgTimeoutNow` and a
  campaign the specification does not model as a transfer. A conf change is out of the workload's
  scope. `MsgSnapStatus`, `MsgForgetLeader` and `MsgReadIndex` would each need a `StepEnd` clause
  (as Q27's `MsgUnreachable` did) for no harness use.

### 3.6 The messages' types at the receiver (G1, G2: found in this pass)

`raft.Step.tracedTriple` needs `StepEndTy m.Type' ∨ AckTy m.Type'`, and the `propc` arm needs a
proposal's entries normal. Slice 30c's table names the source of the type as "the caller's type:
`TrNetTy`…". At the `recvc` arm, though, `netP` gives only `netStepTypes`. That list includes
`MsgReadIndexResp`, `MsgTimeoutNow`, `MsgPreVote`, `MsgSnap` and others. Likewise `fwdP` gives no
entry types. **No statement today supplies either fact.** The design:

- `TrSent st := TrNetTy st.msg.Type' ∨ (st.msg.Type' = MsgProp ∧ ∀ e ∈ st.ents, e.Type' = EntryNormal)`.
- **At the sender**:
  - `rnTrace` keeps `TrOutTy s` with its scope `s.lt = none ∧ ReadIdle s` (§3.2, 1(b)).
  - `acceptReady`'s tokens become `⌜TrSent q.st⌝ ∗ recvTokOf …` for each handed-out `q`. The
    abstraction `outboxRelP` relates `q.st` to an outbox message, so `TrOutTy` gives `TrSent`.
  - `trTok`'s sealed traced body carries the type fact to the client.
- **Through the client**: `node.Step.tracedSpec` hands `trTok` (with `TrSent`) to
  `stepWithWaitOption`. A `MsgProp` goes to `propc` (`fwdP`'s gated normal-entries clause), anything
  else to `recvc` (`netP`'s gated `TrNetTy`).
- **Kept by**: every traced triple on `run`'s path. The new messages of a traced `raft.Step` are of
  `TrNetTy` or forwarded proposals (normal entries, by `PropAny`) for the following reasons:
  - read-index responses are released only from pending reads (`ReadIdle` excludes them);
  - `MsgTimeoutNow` needs `lt ≠ none`;
  - `MsgSnap` is excluded by `TrNoSnap`;
  - pre-votes are excluded by `prevote = false`;
  - forwarded `MsgReadIndex`/`MsgTransferLeader` arise only from stepping those types, which
    `StepEndTy` excludes.

  `ReadIdle` and `lt = none` are themselves kept: only `MsgReadIndex` adds a read and only
  `MsgTransferLeader` sets `lt`, both excluded, and `becomeX` resets `lt`.
- **Where the obligation lands**: `raft.Step.tracedTriple`'s post must say it. Either a new conjunct
  `OutTyStep s s'`, which re-opens slice 30c's assembled proof and gives each path one conjunct; or
  it is derived after the fact from `raft.Step.spec`'s existing `LeaderNonpropResultC` and the role
  results, if they pin the queued types (to be checked per role).

**Flagged §9 (L1)**: the design is argued but not checked against every path's postcondition. It is
raft-internal; no closed or client-visible statement changes beyond the sealed `trTok`'s body.

### 3.7 The booted flag (29n finding 2)

The capability's flag is `b`, under `∃ b` in `rnTrace`.
- `StartNode` returns it unset.
- The `Ready` line (`trCap_fire_ready`, whose post is booted) sets it.
- So do a receive line (`trCap_fire_recv`) and a `BecomeCandidate` (`trCap_fire_any`).

`acceptReady` is the only function that moves `rs.delivered`, and it fires the `Ready` line before
returning. So clause 1(a) of §3.2 (`rs.delivered ≠ [] → b = true`) is established there and kept by
everything else (flags only go up). The `confc` arm reads it. Q19 (a) already lets the bundle and the
ticks run at either flag.

---

## 4. `stepBundle_traced.statement`'s premises (slice 30c's list) and where `run` gets each

`run` calls `raft.Step.traced` from the `recvc` and `propc` arms, from `RawNode.Tick.traced`
(`MsgHup`, `MsgBeat`), and from the traced `RawNode.Advance` (self responses, acknowledgements).

| Premise | Discharged by | From where |
|---|---|---|
| `s.gh.tr = some γd` | `ownRawNode`'s trace field (`%Hgtr`) at a traced cluster | `cluster_alloc_traced` → `StartNode` |
| `s.prevote = false`, `s.cq = false` | `rnTrace`'s scope; `r.[raft,"checkQuorum"] ↦□ false` with `ownRaftPhysC_cq` | `startTrace`'s `TracedConfigOk` |
| `StepEndTy m.Type' ∨ AckTy m.Type'` | `recvc`: `netP`'s gated `TrNetTy` (§3.6) or `MsgUnreachable`/`MsgHup`; `propc`: `MsgProp`; ticks: `MsgHup`/`MsgBeat`; `Advance`: `MsgAppResp`/`MsgVoteResp`/`MsgHeartbeatResp` to self (`TrNetTy`) or `AckTy` | **G1** for the network case |
| `NStateWf s` | `ownRawNode`'s `%Hwf` | — |
| local types at term 0 (`MsgHup`, `MsgBeat`, `MsgProp`, `MsgUnreachable`, `MsgStorageApplyResp`) | the messages' constructors (`hupSt`, `propMsgM`, `ReportUnreachable`'s literal, raft's `tick*`, `newStorageApplyRespMsg`) | — |
| `MsgStorageAppendResp → Term ≤ s.term` | `raft.Step.spec`'s own premise, which `RawNode.Advance` already supplies | — |
| a traced message to `id` | `NetMsgOk`'s `To = id` | `netP` |
| `s.term + 1`, `m.Term` below `traceNumBound` | the ceiling `rs.tc` (`RNPv`: `s.term ≤ s.gh.tc`), bounded by the budget (§3.2); the message's term by `termLB` in `netP` | `budgetInv` |
| `MsgTrOk` | `isRaftMsg_trRecv` (via `netP`'s `isMessage`/`isMessageC`) | the sender's `isRaftMsg` |
| the receipts' fit | the cluster's `readyFits` | `cluster_alloc_traced` |
| no learners | `rnTrace`'s scope (`c.learners = ∅`) | `startTrace` |
| `domSet s.progress ⊆ voters ∪ learners` | `ownRaftPhysC_dom` | — |
| not a pre-candidate | `ownRaftPhysC_precand` with `prevote = false` | — |
| `TrRecvShape` (heartbeat shape, sender in the voters, term not 0) | `isRaftMsg_trRecv` (`SentMsgShape`, `Msg.TrOk`'s heartbeat clauses, Q18/Q28 (c)) | the sender's `isRaftMsg` |
| a proposal's batch non-empty, of normal entries | `propP` (one normal entry); `fwdP`'s gated clause | **G2** for the forwarded case |
| `StepNodeOk s m`: `PrvalsOk s` | `ownRaftPhysC_prvals_ok` | — |
| `StepNodeOk`: `domSet s.prvals = domSet s.progress` | `ownTrackerC_prvals_dom` | — |
| `StepNodeOk`: `MsgAppResp → m.From' ∈ domSet s.progress` | `recvc`'s guard: an unknown sender's response is dropped before `r.Step` (`r.trk.Progress[m.From] == nil`), read with `ownTrackerC_progress_map` | — |
| the recv token `recvTokOf` (a traced type) | `netP`'s gated token (from `node.Step.tracedSpec`'s `trTok`); self responses: `pendingRel`'s `selfTok` | the sender's `acceptReady` |
| (`raft.Step.tracedTriple`) `MsgStorageAppendResp → sn = none`; `MsgStorageApplyResp → ents ≠ [] → c.autoLeave = false` | no snapshot (`TrNoSnap`); no joint configuration at a traced node (bootstrap `AddNode`s only) | — |

Every row but G1 and G2 cites a fact that exists today. G1 and G2 are §3.6's design.

---

## 5. Bootstrap

### 5.1 What raft logs in `StartNode` (A7's check)

`setupNode` runs `NewRawNode` (`newRaft`), then `RawNode.Bootstrap`, then `go n.run()`. On empty
storage it logs, per voter, `|C| + 4` lines, `BootEvAt C i k` at position `k`:

| Position | Line | Logged by |
|---|---|---|
| 0 | `InitState` (term 0) | `newRaft`'s `traceInitState` |
| 1 | `ApplyConfChange` (term 0, empty `newconf`) | `newRaft`'s `switchToConfig` from the empty `ConfState` |
| 2 | `BecomeFollower` (term 0) | `newRaft`'s `becomeFollower(r.Term, None)` |
| 3 | `BecomeFollower` (term 1) | `Bootstrap`'s `becomeFollower(1, None)` |
| `k + 4`, for `k < |C|` | `ApplyConfChange` (term 1, `newconf` a permutation of the first `k + 1` voters, commit and log `|C|`) | `Bootstrap`'s `applyConfChange` per peer, through `switchToConfig` |

All are logged while unbooted, through `trCap_fire_boot`, whose premise is `BootNext C id o e`
(A7). The segments clause `BootSegs C L` in `simInv` is kept (A7, proved).

### 5.2 The traced constructors (not yet; statements to write)

- **`newRaft.tracedSpec`** (`newRaft.spec` today sets `tr := none`):
  - pre: `newRaft.spec`'s pre with `startTrace γ vs cv` and `nodeBoot`;
  - post: `ownRaftPhys` with `s.gh.tr = some γd` and `trCapB (some γd) γ r id c false Φ Λ2`, where
    `Λ2 o := ∃ x, o = some x ∧ BootEvAt C id 2 x`;
  - untraced: today's spec.
  - Proved from `startTrace_trCapB` (A4, proved: the capability once the struct and its logger field
    exist) and the gates. `trCapB_hookGate_init` gives position 0. `traceConfChangeEvent.spec` over
    `RaftReadLend` with `trCapB_hookGate_ccBoot` gives 1. `raft.becomeFollower.traced` at `b = false`
    gives 2. Each gate's `BootNext` premise comes from the previous `Λ`.
- **`RawNode.Bootstrap`'s traced spec**:
  - pre: the capability unbooted at `Λ2`, and `bootMarshal` (Q32);
  - post: unbooted at `Λ_end o := ∃ x, o = some x ∧ BootEvAt C id (|C| + 3) x`.
  - Proved from `raft.becomeFollower.traced` (3) and, per peer, the traced `raft.applyConfChange` →
    `switchToConfig` at a follower (`trCapB_hookGate_ccBoot`, positions `k + 4`). The follower case
    is the only one here; no leader case arises.
- **`NewRawNode`/`setupNode` traced**: thread these. After `Bootstrap`, `simIdle_boot` (slice 21)
  gives the phase `SimIdle C s`. `setupNode` then mints `bootDone tn id` by `trCapB_bootDone` (A8.2)
  at `Λ_end`, and packs `rnTrace`, weakening `Λ_end` to the default `Λ`.
- **`StartNode.gatedSpec`** (A8.3) from `setupNode` and `run`'s spawn (`node.run.spec`, §3.2).

### 5.3 Amendment A8 (Q36 (a), Q37 (a), decided by the coordinator): exact statements

**A8.1: `simInit` (Q36 (a)).** File `TraceSimGhost.lean` (frozen Draft).
- Old: `simInit C := { server := srv, s := fun _ => { v with durable := Etcdraft.durableOf v }, messages := [], pendingMessages := [], reconfigCount := 0 }`.
- **New**: `s := fun i => if i ∈ srv then { v with durable := Etcdraft.durableOf v } else bootJunk`.
  `bootJunk` moves from `TraceSimEnd.lean` to `TraceSimGhost.lean`, above `simInit`; its body is
  unchanged.
- Consequences:
  - `bootInit C` is `simInit C` by definition. Delete `bootInit`, or keep it as an `abbrev` with
    `bootInit_eq : bootInit C = simInit C`. `newTrace_bootInit`'s conclusion becomes `t.init = simInit C`.
  - **Delete** `bootInit_ne_simInit` and `not_bootFacts` (`MainSim.lean`): they become false.
  - New lemma `simInit_s_voter : idAbs i ∈ confAbs C → (simInit C).s (idAbs i) = { v with durable := … }`.
    The users that read a voter's server rewrite by it: `simFx_simInit`, `specInv_simInit`,
    `cfgFixed_simInit`, `startTrace`'s `(simInit vs).s (idAbs cv.ID')`, `voterStart`.
  - `SimRun`'s meaning changes only at non-servers.
- Argument: every reader of `simInit` reads voters' servers only (A7's check). `bootJunk` is a
  follower, so non-server readers (if any appear in a proof) see a follower too.

**A8.2: the completion witness (Q37 (a)).** Files `TraceSimGhost.lean`, `TracedCap.lean` (frozen).
- `structure TraceNames`: old fields `tr st bag voters bt`. **New**: also `dn : GName` (the voters
  whose bootstrap is complete). `traceNames_countable` gains the component.
- New definition: `def bootDone (tn : TraceNames) (i : w64) : IProp GF := ghostMapElem tn.dn i DfracDiscarded ()`,
  with `instance : Persistent (bootDone tn i)`.
- `simInv C tn Fx`: **new** `∃ Dn : GMap w64 Unit` with the conjunct `ghostMapAuth tn.dn 1 Dn` and the
  pure clause `(∀ i, Dn !! i = some () → BootDone C L i)`. Everything else is unchanged.
- New pure lemma `bootDone_snoc : BootSegs C (L ++ [e]) → BootDone C L i → BootDone C (L ++ [e]) i`.
  Argument: if `e` extended `i`'s segment, its length would be `|C| + 5`, and `BootSegs` would need
  `BootEvAt C i (|C| + 4)`, which requires `|C| < |C|`. Each law that re-establishes `simInv` uses it:
  `trCap_fire`, `_any`, `_ready`, `_recv`, `_bf`, `_booted`, `_boot`, and the `Pin`/`Opt` variants.
  They already prove `BootSegs` at `L ++ [e]`.
- New lemma `bootEvAt_pos_unique : BootEvAt C i k x → BootEvAt C i k' x → k = k'`. Each position's
  name, term and `newconf` size differ.
- **New law** (in `TracedCap.lean`, beside `trCap_fire_boot`):
  ```lean
  theorem trCapB_bootDone (γd) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
      (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) (E : CoPset)
      (hE : ↑(simNS γ) ⊆ E)
      (hΛ : ∀ C cs P o, Φ C cs P → Λ o → ∃ x, o = some x ∧ BootEvAt C id (C.length + 3) x) :
      trCapB (some γd) γ r id c false Φ Λ ={E}=∗
        trCapB (some γd) γ r id c false Φ Λ ∗ ∃ tn, traceDir γd tn ∗ bootDone tn id
  ```
  Argument: open `simInv`. The flag is `false`, so `booted L (idAbs id) = false`: every one of
  `id`'s events is bootstrap-named, its segment is all of them, and `LastOf` makes `o` its last.
  `BootSegs` puts the last at position `len − 1`, and `hΛ` at `|C| + 3`. By `bootEvAt_pos_unique`,
  `len = |C| + 4`, which is `BootDone`. Insert `id` into `Dn` and persist the element.
- `Cluster.traceSimInv_alloc` (`TracedApiDraft.lean`) and `Cluster.traceSim_alloc` gain the premise
  resource `ghostMapAuth tn.dn 1 (∅ : GMap w64 Unit)`. `traceNames_alloc` allocates it.

**A8.3: `StartNode` returns the witness.**
- `TracedApiDraft.lean`, new definition:
  `def startDoneB (γ : Cluster) (id : w64) : IProp GF := match Cluster.trace γ with | none => True | some γd => ∃ tn, traceDir γd tn ∗ bootDone tn id`.
- `StartNode.gatedSpec`'s post. Old ends with `peers ↦*{dq} pv`. **New**: `… ∗ peers ↦*{dq} pv ∗ startDoneB γ cv.ID'`.
- `TracedNodeApi.lean`:
  - `StartNode.tracedSpec D` → `StartNode.tracedSpec`, whose post is `startDone γ cv.ID'`, sealed over
    `bootDone`;
  - delete `StartNode.tracedSpec_of_gated`'s parameter;
  - `startDone` drops `D`.

**A8.4: the end law** (`TracedNodeApi.lean`, an API law; replaces the hypothesis `BootEnd D`):
```lean
theorem Cluster.traceSim_bootEnd (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E)
    (hne : vs ≠ []) (hlen : vs.length < 2 ^ 40) :
    (nodeBoot γ N vs ctxs id ∗ Cluster.traceSim γ vs tn ∗ □ ([∗list] i ∈ vs, bootDone tn i) ∗
        traceAuth tn.tr L : IProp GF) ={E}=∗
      traceAuth tn.tr L ∗ ⌜∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.init = simInit vs ∧
        t.server = confAbs vs ∧ t.initSrv = confAbs vs⌝
```
Proved by opening `simInv`: each `bootDone tn i` is in `Dn`, so `BootDone vs L i`. With `SimRun`,
`SimEvents` and `BootSegs`, `newTrace_bootInit` and A8.1 give the result. The conclusion is
`BootFacts vs L`'s body. `HarnessEnd.lean`'s `BootEnd` becomes a theorem `bootEnd` at
`D := bootDone`, gaining `hne`/`hlen`, which the harness has: `vs = [1,2,3]`.

No change to `trCap_fire_boot`, `BootSegs`, `BootNext`, the capability `trCapB`, or any other law's
statement (their proofs add one conjunct each). A8 needs its own review round and re-freeze
(`trace-check-frozen-a8`), as A4-A7 did.

---

## 6. Q33, Q34, Q35

**Q33 (`strconv.Itoa`).** Perennial translates `strconv` with bodies only for `ParseUint` and its
errors (`Perennial/Code/strconv.toml`); `Itoa` is names-only. **This repository already has a
trust-boundary spec and axiom**: `Spec/strconv/Itoa.lean` (`strconv.Itoa.spec`: returns
`fmtInt i (W64 10)`) and `Proof/strconv/Itoa.lean` (`axiom strconv.Itoa.wp_proof`, in
`etc/tcb-baseline.txt`). They were added for the k8s compactor example (K4).
- **Decided here: the proposer uses it.** It is an existing axiom of the trust base's
  standard-library kind (the plan's "Trust base" already lists `strconv.FormatUint`), so the exit
  criterion's "only the trust base's existing axioms" holds. The tracecheck TCB collection's
  baseline gains the line (an update, recorded when it happens). The trust base itself does not
  change.
- `notes/perennial-changes.md`'s entry ("Workaround here: none yet") is stale. The workaround is
  this axiom; the proposed Perennial change (translate `Itoa`/`FormatInt` and prove the spec) stands.
- Nothing is needed of the string but that it exists. `[]byte(...)` and `+` are primitives.

**Q34 (the network's wait group: several adders, unbounded).** This is a harness-local idiom over
the raw `WaitGroup` specs, backed by thread tokens (CLAUDE.md "Bounds"; Perennial's `tokJoin` is the
model). File `Proof/.../tracecheck/NetJoin.lean`.
- **Names**: `netJoin` names `γ.wg : WaitGroupNames`, `γ.dep` (the slots' token count), and `γ.ad`
  (the adders' fraction).
- **Invariant**: `njInv γ := ∃ ctr j, ownWaitGroup γ.wg ctr ∗ threadToks j ∗ ownTokAuth γ.dep j ∗ ⌜sint.Z ctr = j⌝ ∗ (ownWaitGroupWaiters γ.wg 0 ∨ dghostVar γ.ad (DFrac.own 1) ())`.
  `isNetJoin N wg γ := isWaitGroup wg γ.wg (N.@"wg") ∗ inv (N.@"inv") (njInv γ) ∗ ⌜threadBound GF ≤ 2^31⌝`.
- **Rights**: `njAdder q := dghostVar γ.ad (DFrac.own q) () ∗ isNetJoin` (fractional). `njDone := ownToks γ.dep 1 ∗ isNetJoin`.
- **Laws**:
  - `nj_init`: from a fresh wait group, `njAdder 1`.
  - `njAdder_split`.
  - `netJoin.wp_Add`: `{njAdder q ∗ threadTok} wg.Add(1) {njAdder q ∗ njDone}`.
    - Argument: open `njInv` at `⊤`. An adder with `q > 0` refutes the right disjunct (full
      fraction), so `ownWaitGroupWaiters 0` is there for `Add`'s `oldc = 0` case and goes back.
    - The token is deposited, and `ctr + 1 = j + 1`.
    - `threadToks_add_one_lt` gives `j + 1 < threadBound ≤ 2^31`, which is `Add`'s bound.
  - `netJoin.wp_Done`: `{njDone} wg.Done() {threadTok}`.
  - `njClose`: `njAdder 1 ={⊤}=∗ ownWaitGroupWaiters γ.wg 0`. It puts the full fraction in and takes
    the left disjunct out.
  - `netJoin.wp_Wait`: from the waiters' token, by `alloc_wait_token` then the raw `Wait`, as
    `tokJoin.WaitGroup.wp_Wait_of`.
- **Thread tokens**: `app` deposits a thread token at each `Add`, and the `go` gives the parent a
  fresh one (`wp_fork_tok_self`, as `tokJoin`).
- **`threadBound GF ≤ 2^31`**: from the `ThreadBoundLe` instance, as `newCache.wp_proof` does. This
  is to be confirmed at `tcGF` in Probe. Otherwise it is a premise of `RunConcurrent.spec` (not of
  the closed theorem), discharged in `tracecheck_adequate_of` by the adequacy's choice of the bound.
- `etc/bounds-allow.txt` lists the idiom's own matches (it is the owner).
- **Perennial**: the general shared-adder join (fractions of `ownAdder`) is recorded in
  `notes/perennial-changes.md` (S7 part 2) and is proposed independently. The local idiom is the
  workaround.
- The same file gives `join3` for `drivers.Add(3)`, a fixed count: three `ownDone`s from one raw
  `Add` with `oldc = 0` and the waiters' token held by the single adder. This is the
  `WaitGroupJoin` argument at delta 3.

**Q35 (`Workload`'s `Tick > 0`).** Taken, (a): §2.1. It is layer D's own predicate. It is not in the
closed statement (§1.3 is stated at `defaultCConfig`).

---

## 7. The chain, every statement: proved from, and why that suffices

★ = not proved today. † = flagged in §9.

| Statement | Proved from (callee statements) | Why it suffices |
|---|---|---|
| `raft_tracecheck_safe` (§1.2) | `tracecheck_adequate_of` (new binders threaded), `tcMainSpec` | adequacy turns `Main`'s spec at every `HeapGS` into the operational statement. `Hprem` is instantiated at each `hG`, as in putget |
| `raft_tracecheck_accepts` (§1.3) | `RunConcurrent.spec` at `defaultCConfig` (`Workload defaultCConfig` by `decide`), `tracecheck_Events_traceAccepts` | the post `runOver c` is exactly the latter's precondition |
| `tcMainSpec` / `Main.spec` ★(premises) | `Main.wp_proof` (proved) with `RunConcurrent.spec` and the Link's checker specs | unchanged proof, plus passing `premises boot` |
| `RunConcurrent.spec` ★ | §2.2's calls: `harness_alloc`, `startTraceC_intro`, `StartNode.tracedSpec`, `sync.join`, `join3`, `netJoin`, `app`/`send` (below), `node.Stop.spec`, `runOver_intro` with `Cluster.traceSim_bootEnd` | allocation gives each voter's `startTraceC`; the three `bootDone`s and `Cluster.traceSim` give `BootFacts`; `runOver_intro` composes |
| `app` ★ (harness-local spec: `isNode`, driver state, `nodeRunning 1`, `njAdder ⅓`, `ownDone apps …`) | `time.NewTicker`, `node.Tick.spec`, `isReadyChan_recvAu.tracedSpec`, `handleReady`, `node.Advance.tracedSpec`, `send` | loop invariant: the driver state idle, `nodeRunning 1`, `njAdder ⅓`. Each `Ready` round: the claim from the receive, the tokens at `Advance`, one `send` per token |
| `handleReady` ★ | storage contract, `proto.Unmarshal`, `node.ApplyConfChange.spec` | as kvreconf's handler. Snapshot branches dead |
| `send` ★ | `netJoin.wp_Add`, `trTok_type`, `node.Step.tracedSpec`, `node.ReportUnreachable.spec`, `netJoin.wp_Done` | the token rides into the goroutine. `ReportSnapshot` is dead by `trTok_type` |
| `netJoin` laws, `join3` ★ | raw `WaitGroup.Add/Done/Wait`, `alloc_wait_token`, `threadToks_add_one_lt` | §6. `tokJoin`'s argument with fractional adders |
| `StartNode.tracedSpec` ★ (A8.3) | `StartNode.gatedSpec` (Draft, amended), `startTraceC_eq` | the client statement is the Draft's over the sealed names (as today's `tracedSpec_of_gated`) |
| `StartNode.gatedSpec` ★ | `setupNode` traced, `node.run.spec` (the spawn) | `setupNode` returns the node with `bootDone` and `runPre`; `go n.run()` with `node.run.spec` |
| `setupNode`/`NewRawNode` traced ★ | `newRaft.tracedSpec`, `RawNode.Bootstrap` traced, `trCapB_bootDone`, `simIdle_boot` | §5.2 |
| `newRaft.tracedSpec` ★ | `startTrace_trCapB` (proved), `trCapB_hookGate_init`/`_ccBoot` (proved), traced `traceConfChangeEvent.spec` ★ (`RaftReadLend`), `raft.becomeFollower.traced` (proved) | positions 0-2 by `BootNext` from each previous `Λ` |
| `RawNode.Bootstrap` traced ★ | `raft.becomeFollower.traced`, `bootMarshal`, traced `raft.applyConfChange` ★ (follower, `_ccBoot`) | positions 3 to `|C| + 3` |
| `trCapB_bootDone` ★ (A8.2) | `simInv`'s `Bt`/`LastOf`/`BootSegs`, `bootEvAt_pos_unique` | §5.3 |
| `Cluster.traceSim_bootEnd` ★ (A8.4) | `simInv`'s new clause, `newTrace_bootInit`, A8.1 | §5.3 |
| `isReadyChan_recvAu.tracedSpec` ★ (revised) | `isReadyChan`'s channel protocol with `readyP` carrying the claim half | the claim half is in `readyP` at `run`'s send (§3.2, 2.). No token is needed at the receive |
| `node.Advance.tracedSpec` ★ | `advInv` with the deposit (§3.2, 4.) | the driver's claim agrees with `run`'s half; the tokens are in `advDep` or `RcvCommit` |
| `node.Step.tracedSpec` ★ | `stepWithWaitOption` with `netP`/`fwdP` gated (§3.2, 5.-6.) | `trTok`'s `TrSent` sends a `MsgProp` to `fwdP` (normal entries) and the rest to `netP` (`TrNetTy` with the token) |
| the five refused `node.X.spec`s (§3.5) | unchanged proofs, plus the premise discharging `netP`'s/`propP`'s untraced arm | untraced `netP` is unchanged |
| `node.run.spec` (one spec) ★ | §3.2's arms: `raft.Step.traced` with `stepBundle_traced` (proved), `wp_rn_raft_Step_prop_traced` (proved), `RawNode.Tick.traced` (proved), `acceptReady.spec` (proved), traced `RawNode.Advance` ★, traced `raft.applyConfChange` ★† (leader case), `getStatus` | the invariants of §3.2 (1.-6.) give each arm's premises (§4); the bounds by the budget |
| traced `RawNode.Advance` ★ | `raft.Step.traced` (self responses: `TrNetTy`, `selfTok`), `stepBundle_traced` on `AckTy` (`.onA`, `stepBundle_traced_storAck`, proved), `TrNoSnap` | 28n's design. `stepsOnAdvance` holds exactly the self responses and the two acknowledgements (`acceptReady`'s Go) |
| traced `raft.applyConfChange` / `switchToConfig` ★† | `Changer` specs giving back the old maps, `traceConfChangeEvent.spec` over `RaftReadLend` ★, `trCapB_hookGate_applyCC` (proved, booted) / `_ccBoot` (unbooted) | follower case argued (29n). Leader case: §3.4 |
| `rnTrace`'s new clauses (flag to delivery, `TrOutTy`, `lt = none`, `ReadIdle`, `role ≠ follower → applied ≥ |boot|`) ★† | established at `setupNode`; kept by `acceptReady` (flag), `raft.Step.traced` (types: needs a post conjunct or a derivation, §3.6), `hup` (applied) | §3.6, §3.4 |
| `raft.Step.traced`, `stepBundle_traced` | proved (30c) | — (gains `OutTyStep` if §3.6's first option is taken: †) |
| `RawNode.Tick.traced`, `acceptReady.spec`, `readyWithoutAccept.spec`, `wp_rn_raft_Step_prop_traced`, `trCapB_hookGate_applyCC`, `traceConfChangeEvent.tracedSpec_proof`, `startTrace_trCapB`, `cluster_alloc_traced`, `harness_alloc`, `Cluster.traceSim_alloc`/`_end`, `runOver_intro`, `tracecheck_Events_traceAccepts`, the checker's Link | proved | — |

---

## 8. The end-to-end probe (after review)

**The path, in the Go's order.** The task named `StartNode`, `Ready`, `send`→`Step`, then
`Advance`; in the harness `Advance` comes before `send`.

1. `StartNode` for voter 1 (bootstrap: `|C| + 4` lines, `bootDone tn 1` returned).
2. `app`: `node.Ready` receive.
3. `handleReady`.
4. `node.Advance`: the tokens for the `Ready`'s messages.
5. `send`, then `node.Step` at voter 2.

The first `Ready` of a fresh voter hands out no message (a term-1 follower has sent nothing). So the
concrete run that reaches a message is:
- `StartNode` ×3;
- voter 1's first `Ready` (the three bootstrap entries; `ApplyConfChange` ×3; `Advance`);
- ticks until `tickElection` campaigns;
- voter 1's second `Ready` with `MsgVote` to 2 and 3;
- `Advance`, giving `trTok` for each `MsgVote`;
- `send` → `node.Step` at voter 2;
- voter 2's `recvc` arm steps the `MsgVote` (`TrNetTy`) and logs the receive line after voter 1's
  `Ready` line.

**Probe A (client glue, harness level; easy).** A Lean `example` over the client statements as
hypotheses:
- `harness_alloc`, then `startTraceC_intro`;
- `StartNode.tracedSpec` (A8.3) for one voter;
- `isReadyChan_recvAu.tracedSpec` (revised), giving `readyGotT` with the claim on `ms`;
- `node.Advance.tracedSpec`, giving `[∗list] q ∈ ms, trTok γ q.st`;
- for `q ∈ ms`: `trTok_type`, then `node.Step.tracedSpec` at `q.msg.To'`;
- at the end, `Cluster.traceSim_bootEnd` with the three `bootDone`s, then `runOver_intro`.

It checks that each statement's post supplies the next one's pre: the claim's `ms` against
`readyGot`'s `ms` and `rd.Messages`; `trTok` against `node.Step.tracedSpec`'s `st` after
`proto.Clone`; `bootDone` into `BootEnd`.

**Probe B (node level; hard, chosen by its invariant).** The new invariant is the token deposit in
`advInv` with the claim (§3.2, 2.-4.), plus `netP`'s gated token and type (§3.6). Prove, for one
node, the composition:
1. `run`'s `readyc` arm: the claim half into `readyP`, then `acceptReady.spec` (its `"Htoks"`).
2. The busy loop state.
3. The `advancec` arm's rendezvous in both orders (`RcvPending` and `SndPending`), which must yield
   `node.Advance.tracedSpec`'s tokens.
4. At the receiver, the `recvc` arm from `netP` (gated) through the guard to `raft.Step.traced` with
   `StepNodeOk` and the token.

This is the riskiest piece: it checks that the claim, the deposit and the `rtk` halves close in both
rendezvous orders and come back whole for the next `Ready`. It also checks that `TrOutTy` gives
`TrSent` at `acceptReady` (G1's sender half).

---

## 9. Links not argued, and decisions

**Links I could not argue in full** (all raft-internal; none touches §1):
- **L1 (G1, G2; §3.6). The network messages' types and a forwarded proposal's normal entries at a
  traced receiver.** No statement supplies them today: slice 30c's table assumes "the caller's
  type". The design is `TrOutTy` in `rnTrace` with its scope (`lt = none`, `ReadIdle`), carried as
  `TrSent` in `trTok`/`netP`/`fwdP`. The unargued part is its preservation through
  `raft.Step.traced`: either a new post conjunct (re-opening 30c's assembly, one conjunct per path)
  or a derivation from `raft.Step.spec`'s role results, not yet checked against each path's queued
  messages.
- **L2 (§3.4). `switchToConfig`/`applyConfChange` at a leader in the `confc` arm.** The line lemma
  `trCapB_hookGate_applyCC` needs `AccIdle` (not a leader), so 29n's "prove the leader case with
  existing pieces" lacks the `ApplyConfChange` line itself. Excluding the leader case (`hup`'s
  refusal while conf entries are unapplied, plus A1 at `Advance`) is argued but not checked; in
  particular step 3 (A1 gives `k + 1 > raftLog.applied` at the `confc` arm) needs a reading of
  `undecFree`/`cam` against `raftLog.applied`.
- **L3 (§3.5). The refused calls' premise `Cluster.trace γ = none`** on five client-visible node
  specs. It is argued (gated pure fact, allowed by the acceptance test), but the number of etcd-server
  call sites that must thread it is not counted yet.
- **L4 (§6). `threadBound GF ≤ 2^31` at `tcGF`**: from `ThreadBoundLe`, to confirm.

**Decisions taken in this pass (the agent's, recorded in `notes/decisions.md`, "Design pass (node
API, harness)"):**
- the tokens come at `node.Advance` through a claim (29n finding 4's proposal, made exact: the
  deposit in both rendezvous orders);
- the gated client statements, each with its untraced instance as today's spec;
- `TrSent` in the sealed `trTok`, and `trTok_type`;
- the five refused calls;
- the leader case of `confc` excluded rather than proved;
- A8's exact form;
- Q33 by the existing `strconv.Itoa` axiom;
- Q34's local `netJoin` and `join3`;
- Q35 (a);
- the corollary stated at `defaultCConfig`.

**The user's:** only §1. Q32 is already decided (the premise bundle). The new item for review is
the corollary's form (§1.3), which had no stated form before. No other change to a closed statement
or to the trust base is proposed.
