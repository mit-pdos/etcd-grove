# Trace-check: the design pass, from the closed theorem down to the proved pieces (2026-11-11, revision 1)

The user approved this pass (2026-11-11) under `notes/spec-first-plan.md`'s *Design before plumbing*:
before more threading, the whole chain is written as text, each statement with what it is proved
from and why that suffices, for review. Nothing here is threaded or proved. Every Lean
statement below is a text sketch, **not typechecked** (no Lean was run). Old → new is given wherever
a statement exists today. Revision 0: branch `trace-check-design`, from `trace-check` at `c2325abf53`.
Revision 1: branch `trace-check-design2`, from `trace-check` at `886be91e1b`, after the review round
`notes/trace-validation-reviews/design-r1.md` (first tier F1-F3, second tier S1-S12).

Reading order: §1 is the only part the user reviews (settled: Q32 and Q38 decided by the user). §2-§6
are the agent's (intermediate statements, recorded per "The gates, delegated"). §7 is the whole chain
as one table. §8 is the probe to run after review. §9 lists the links that are not argued, the order
of work that keeps every existing result proved, and the decisions.

Vocabulary used throughout: `TrNetTy t` (`MsgApp`, `MsgAppResp`, `MsgVote`, `MsgVoteResp`,
`MsgHeartbeat`, `MsgHeartbeatResp`), `AckTy` (`MsgStorageAppendResp`, `MsgStorageApplyResp`),
`recvTokOf` (`TracedRecvTok.lean`), `trTok` (today `TracedNodeApi.lean`; revision 1 moves it to
`InvNode.lean`, §3.1), the capability `trCapB` (`TracedCap.lean`), `rnTrace` (`InvRawnode.lean`).

---

## Revision 1 (2026-11-11): what each finding of `design-r1.md` changed

**First tier.**
- **F1 (the step bound; the thread bound).** Taken: Q38 (a), **decided by the user (Q38,
  2026-11-11)**. §1.2's `Hn` is `n + 2 ≤ 2 ^ 31` (was `n + 4 ≤ 2 ^ 61`); §1.3 gains
  `[ThreadBoundLe GF (2 ^ 31)]`; `RunConcurrent.spec`, `Main.spec` and `tcMainSpec` take the instance
  (§2.1); `tracecheck_adequate_of` derives it (`ThreadBoundLe.of_eq HT`, weakened by `Hn`) and the old
  `receiptBound GF + 3 ≤ 2^61` from `HN` (§2.1). `isNetJoin` no longer carries a pure bound: `netJoin.wp_Add`
  reads the instance (§6). The chain is checked end to end in §6 ("The thread bound, end to end"). L4
  (revision 0's) is closed.
- **F2 (`node.Step`).** Taken: the review's fix. One proved spec, `node.Step.spec`, text unchanged. The
  gate moves into `stepIn`'s sealed body (`stepP`'s traced `netP`/`fwdP` need the token and the type);
  `stepIn_intro` gains the premise `trTok γ st`, which untraced clients discharge with
  `trTok_untraced γ st h`. `node.Step.tracedSpec` becomes a corollary (`stepIn_intro` + `node.Step.spec`).
  The four call sites of `stepIn_intro` each hold `h` already, but kv's (one new conjunct in kv's own
  `kvPeerOk`) (§3.1, "F2's call sites"). Found while checking: `node.ProposeConfChange` builds `stepIn`
  internally (not through `stepIn_intro`) for a conf-change `MsgProp`, so under the gated `stepIn` its
  refusal premise is **needed**, not redundant (S10's second point does not hold).
- **F3 (`node.Advance`).** Choice: **a fresh claim per `Ready`, `run` needing nothing back**, which
  changes no client; `node.Advance.spec` keeps its text and is proved for every `γ`. The review's
  sketch of it was not sound as written: a claim named by a fresh ghost name agrees with nothing the
  deposit names, and a driver can keep a stale claim (from a `Ready` it advanced with
  `node.Advance.spec`). Revision 1 makes it exact with a per-node escrow (`rtkInv`) at fixed names and an
  exclusive "no deposit pending" token that `run` lends at the rendezvous (§3.2 items 2-4), and argues it
  against `node.go`'s `run` (`advancec` is armed only in the `readyc` arm after `acceptReady`). The
  alternative (`Cluster.trace γ = none →` on `node.Advance.spec`, "both halves back") is the fallback,
  costed in L3.

**Second tier.**
- **S1.** §2.2's conf-change proposer row corrected: `time.Now()` (`concurrent.go:206`) and
  `time.Time.Add` are called once, before the loop; only the loop's `time.Now().Before` and `Status`
  are short-circuited. §6 ("What the closed theorem rests on") lists every existing axiom the closed
  theorem rests on once `RunConcurrent` is proved: raft's node-API path's fifteen (`etc/tcb-collections/raft.txt`'s
  baseline, `strconv.Itoa` among them), the harness's own `proto.ClonePb.wp_proof` (revision 0 wrongly said
  "`proto.Clone` as kvreconf": kvreconf copies messages by hand), and Perennial's trusted `time.Now`. None
  is new.
- **S2.** A8.2 uses the existing `bootEvAt_unique` (`TraceSimBootSeg.lean:218`); no copy.
- **S3.** `startDone γ i` stays sealed; the end law `Cluster.traceSim_bootEnd` and `HarnessEnd`'s
  `runOver_intro` take `□ [∗list] i ∈ vs, startDone γ i` with `traceDir γd tn` and
  `Cluster.trace γ = some γd`, and do the `traceDir` agreement inside (A8.4).
- **S4.** §5.2's statements written at the voters' configuration `cC` (not raft's `c`, empty at
  positions 0-2), with the phase `Φvs C _ _ := C = vs`, so that `Λ2`/`Λend` written at the caller's `vs`
  discharge `trCapB_bootDone`'s `hΛ`.
- **S5/S9.** §3.3 lists every proved triple a new `rnTrace` clause re-opens; §9 "Order of work" puts
  every gate in with its `none` arm equal to today's body, so the untraced proofs (all of today's
  results) are re-proved by rewriting the gate and no `sorry` goes under an existing result; the traced
  `node.run` is a separate theorem with the ★ arms as hypotheses until they are proved; `node.run.spec`'s
  premise is dropped only then (its untraced statement kept as an instance).
- **S6.** §3.4 restates the leader obstacle: `AccIdle` says nothing of the role; at a leader
  `switchToConfig` also logs `Commit` (`maybeCommit`) and sends (`bcastAppend`), which
  `trCapB_hookGate_applyCC` (phase `SimIdle`) covers neither.
- **S7.** §3.4 states the exclusion's lemmas: the bootstrap log prefix, the `confc`-arm lemma, and a
  third found here (no conf entry past the bootstrap log at a traced cluster, G3). L2 updated.
- **S8.** `tracecheck.BootFacts` renamed `tracecheck.BootLogFacts`.
- **S10.** L3 counted (§9): the refused calls, `Step` (through `stepIn_intro`) and, in the fallback only,
  `Advance`. `ReportSnapshot` keeps its refusal premise (other clients at a traced cluster could call it;
  the harness's call is dead by `trTok_type`); `ProposeConfChange` keeps its premise (F2 above).
- **S11.** A8.2's list of `simInv` re-establishers gains `trCapB_perm` (`TracedFamilies.lean`, `L`
  unchanged, the clause carries trivially) and `Cluster.traceSimInv_alloc` (the empty `Dn`); the
  readers (`TraceSimEnd`'s `simInv_end`, `simInv_end_boot`) only drop the conjunct.
- **S12.** §2.2 names the harness's invariants: `tcOpsInv` (`ownCommittedOps`, outside `N`, building
  `Propose`'s AU per call) and the shared decision authority as raft's own client library
  `confPolicy` (`ConfPolicy.lean`, `confPolicy_alloc`/`confPolicy_decide`, as kv's `kvRule`), and
  `tcSnapsInv` (`ownSnapsMade γ []`). `handleReady`'s snapshot branch is refuted from client-visible facts
  (`readySnap`'s `snapshotCert`, `snapshotCert_made`, `snapMade_elem` against `ownSnapsMade γ []`), not
  `TrNoSnap`. `γ.rtk` is per node (`NodeNames` fields, §3.2). `readyToksClaim`'s docstring states the
  departure from "no identification handles" with the alternative. A8.1 keeps `bootInit_eq` as a lemma
  (propositional, not definitional).

**Re-checked.** L1 (the outbox's types, against `rawnode.go`'s `readyWithoutAccept`/`acceptReady`: the
handed-out messages are `r.msgs` and the non-self `msgsAfterAppend`), L2 (three lemmas now), L3
(counted), §7's provenance column, §8's probe (to the revised chain). New in this revision: **L5**, the
source of `rnTrace`'s `TrNoSnap` at `setupNode` (Q6 item 8's gated `storBnd`, not in revision 0).

---

## 1. The closed statements (THE USER REVIEWS ONLY THIS SECTION; settled)

Both go in `Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/Results.lean`. They replace
`raft_tracecheck_safe_of` (which takes `TcOpen`) once `RunConcurrent.spec` is proved.

### 1.1 The premise bundle (Q32, the user's decision, 2026-11-11)

Modelled on `etcd_putget.BootFacts` and `etcd_putget.premises` (`examples/etcd/putget/Defs.lean`).
New file `Proof/.../tracecheck/Defs.lean`:

```lean
/-- The bootstrap log `StartNode` builds for the peers `1, 2, 3` (each `Peer{ID: i}`, `Context`
nil), as Go computes it: three conf-change entries of term 1 whose data is the marshalled
`ConfChange{Type: AddNode, NodeID: i}` (the node API's `BootLog`). Named apart from layer B's
`TraceCheck.BootFacts C L` (`MainSim.lean`, over `newTrace`). -/
abbrev tracecheck.BootLogFacts (boot : List LogEntry) : Prop :=
  BootLog [W64 1, W64 2, W64 3] [[], [], []] boot

/-- **`Main`'s named premise** (Q32): `proto.Marshal`'s contract at the bootstrap log's conf
changes. Each of the three `StartNode`s marshals `AddNode i`, and the call returns the bytes of
`boot`'s `i`-th entry (`bootMarshal`, persistent). Raft's proof needs the three voters' logs to be one
committed log. `proto.MarshalConfChange.spec` gives only bytes that decode to the change. -/
abbrev tracecheck.premises (boot : List LogEntry) : IProp GF :=
  bootMarshal [W64 1, W64 2, W64 3] [[], [], []] (LogEntry.toEntries boot 0)
```

No axiom changes (Q32: "follow the etcd examples"). The bundle holds `bootMarshal` only.

### 1.2 `raft_tracecheck_safe` (the closed theorem)

```lean
theorem raft_tracecheck_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [hLog : log.NewModel]
    (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot)
    (Hprem : ∀ hG : HeapGS .hasLC tcGF,
      ⊢ tracecheck.premises (GF := tcGF) (hG := heapWith hG lctx) boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n + 2 ≤ 2 ^ 31) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([tracecheckProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

**What changes from `raft_tracecheck_safe_of`'s statement:** `hopen : TcOpen` is gone. Three
binders are added: `boot`, `Hbf` and `Hprem` (Q32). The step bound is `n + 2 ≤ 2^31` (**decided by
the user (Q38, 2026-11-11)**; was `n + 4 ≤ 2^61`). In plain terms: the harness starts one goroutine per
message and counts them in a `sync.WaitGroup`, which panics past `2^31`; the proof bounds the
goroutines by the run's length, so the theorem covers runs of fewer than about `2^31` steps (it
implies the old `n + 4 ≤ 2^61`; `etcd_putget_safe` has `n + 2 ≤ 2^28`). Everything else is word for
word: the program, the three conclusions and the instance context. `tracecheckProgram` is the
package's initialization, then `Main()`; `Main` runs `RunConcurrent(DefaultCConfig())`,
`ConvertEvents`, `NewTrace`, and `CheckTrace(tr, true)`, and panics unless `TLCOK`.

### 1.3 `raft_tracecheck_accepts` (the corollary: every run's trace satisfies `TraceAccepts`)

`TraceAccepts` is unchanged (`etcdraft/Tla/Check.lean`):
`TraceAccepts events pv cq := ∃ t, newTraceWith events pv cq = .ok t ∧ ∃ res, CheckTraceRel t true res ∧ res.tlcOK = true`.

```lean
theorem raft_tracecheck_accepts [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [ThreadBoundLe GF (2 ^ 31)]
    (Hrb : receiptBound GF + 3 ≤ 2 ^ 61) (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
        context.isClosedchanInit ∗ tracecheck.premises boot }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent))
        (Val #defaultCConfig))
    {{ (c : Loc), RET (PairV #c #interface.nil);
        WP (App (Val (c @!! go.GoType.PointerType Cluster.ty @!! go!"Events")) (Val #()))
          {{ v, ∃ (sl : GoSlice) (L : List TraceEv), ⌜v = #sl⌝ ∗ traceEventsRep sl L ∗
                ⌜Etcdraft.TraceAccepts (L.map TraceSim.evConv) false false⌝ }} }}
```

The composition of `RunConcurrent.spec` (§2.1) with the proved `tracecheck_Events_traceAccepts`, at
`defaultCConfig` (so the closed statement does not expose `Workload`). The form is **approved by the
user (Q38, 2026-11-11)**; the instance `[ThreadBoundLe GF (2 ^ 31)]` is Q38 (a).

**Nothing else in the chain below is the user's.** The trust base is unchanged: no axiom is added.
§6 lists the existing axioms the closed theorem will rest on.

---

## 2. `RunConcurrent` and the harness: what each piece uses from the node API

### 2.1 The harness's own statements (layer D, the agent's)

- **`Workload`** (`Spec/.../tracecheck/RunConcurrent.lean`). Old: three voters, no extra node, no
  configuration change, no snapshot, `0 ≤ MaxDelay < 2^62`. **New** (Q35 (a)): add
  `0 < sint.Z cfg.Tick'`. `time.NewTicker` panics otherwise. `DefaultCConfig`'s 10ms meets it.
- **`RunConcurrent.spec`**. Old:
  `receiptBound GF + 3 ≤ 2^61 → ∀ cfg, Workload cfg → {{ isPkgInit ∗ context.isClosedchanInit }} RunConcurrent #cfg {{ c, RET (c, nil); runOver c }}`.
  **New**: `∀ [ThreadBoundLe GF (2 ^ 31)], receiptBound GF + 3 ≤ 2^61 → ∀ boot, tracecheck.BootLogFacts boot → ∀ cfg, Workload cfg →`
  with `tracecheck.premises boot` added to the precondition. `runOver c` is unchanged.
- **`Main.spec`**. **New**: `∀ [ThreadBoundLe GF (2 ^ 31)], receiptBound GF + 3 ≤ 2^61 → ∀ boot,
  tracecheck.BootLogFacts boot → {{ isPkgInit ∗ context.isClosedchanInit ∗ tracecheck.premises boot }} Main #() {{ RET #(); True }}`.
  `Main.wp_proof` passes the three through to `RunConcurrent`.
- **`tcMainSpec`** (`Adequacy.lean`): `∀ [hG] [go.Semantics] [Assumptions], TraceCheck.Main.spec`
  at `tcGF` (the new binders inside `Main.spec`).
- **`tracecheck_adequate_of`** gains `boot`, `Hbf`, `Hprem` and `Hn : n + 2 ≤ 2^31` (was `n + 4 ≤ 2^61`).
  Its proof takes `HT : threadBound GF = n + 2` from `init_adequate` (ignored today, `fun hG HN _`),
  makes `haveI : ThreadBoundLe tcGF (2 ^ 31) := ThreadBoundLe.weaken (n + 2) (of_eq HT) Hn` (or
  `⟨by rw [HT]; omega⟩`, as `cache/Results.lean`), `Hbound : receiptBound tcGF + 3 ≤ 2^61` by
  `rw [HN]; omega` from `n + 4 ≤ 2^31 + 2 ≤ 2^61`, and `ihave #Hprem' := Hprem hG` as
  `etcd_putget_adequate` does.
- **`TcOpen`** is deleted once `RunConcurrent.wp_proof` exists. `Results.lean` then states §1.

### 2.2 `RunConcurrent`'s body (`concurrent.go`), call by call

The harness's own invariants (named here, S12), allocated after `harness_alloc`, all outside `N`
(raft's namespace):
- **`tcOpsInv γ := inv tcOpsN (∃ ops, ownCommittedOps γ ops)`**, from `harness_alloc`'s
  `ownCommittedOps γ boot`. `γ.dup = false`, so `node.Propose.spec` takes one non-persistent AU per
  call, `AU <{ ∃∃ ops, ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅ <{ ∀∀ t, ownCommittedOps γ (ops ++ [⟨t, 0, data⟩]), COMM True }>`;
  the proposer builds it from `tcOpsInv` (open, take, close with the appended list). Nothing else of
  the run reads the committed operations.
- **`confPolicy γ tcConfN tcRule`**, from `harness_alloc`'s `ownConfDecisions γ ∅` by `confPolicy_alloc`
  (`ConfPolicy.lean`, raft's client library, the one kv uses), with `tcRule := fun _ _ e => ccDecode e`
  (kv's `kvRule`). Persistent, so the three `app`s share it: each `handleReady` obtains
  `confDecided γ k (.apply o')` for a committed conf entry by `confPolicy_decide` (the recorded decision
  if another `app` decided position `k` first, the same at every caller), with `confAt γ k m` from
  `harness_alloc`'s `confAt γ 0 …` and each `ApplyConfChange`'s post, as kv's `applyConf`.
- **`tcSnapsInv γ := inv tcSnapsN (ownSnapsMade γ [])`**, from `harness_alloc`'s `ownSnapsMade γ []`.
  The harness never makes a snapshot (`SnapshotEvery = 0`); `handleReady` opens it to refute a
  snapshot `Ready` (§2.3).

| Go | Statement used | Old → new | What the proof needs from it |
|---|---|---|---|
| `&Cluster{…}`, `&SyncRecorder{}`, `make(chan struct{})` | Goose allocation; the recorder's lock (`isSyncRecorder`, S7 part 1) | unchanged | the trace's two halves: `traceFrag γt []` to the names, `traceAuth` under the lock |
| (ghost) | `harness_alloc` (`HarnessAlloc.lean`): `traceNames_alloc`, `cluster_alloc_traced`, `Cluster.traceSim_alloc`; then `tcOpsInv`, `confPolicy_alloc`, `tcSnapsInv` | `traceNames_alloc` also allocates `ghostMapAuth tn.dn 1 ∅` (A8.2) | the traced cluster `γ`, `traceDir γd tn`, `Cluster.traceSim γ vs tn`, each voter's `voterStart` |
| `raft.NewMemoryStorage()`, `&raft.Config{…}` | the storage contract (`restartStorage`, as kvreconf) | the storage bound `storBnd` gated (Q6 item 8, L5): no compaction right at a traced cluster | `ConfigValid`, `TraceLogger ≠ nil` (`c.rec`), `MaxSizePerMsg = ^0`, `AsyncStorageWrites = false` |
| `raft.StartNode(rc, peers)` ×3 | `StartNode.tracedSpec` (`TracedNodeApi.lean`) | **`D` fixed** (A8.3): the post's `startDone γ D cv.ID'` becomes the sealed `startDone γ cv.ID'` | `isNode`, `nodeDriver … init`, `nodeConfig`, `nodeRunning 1`, the persistent `startDone` |
| `c.apps.Add(1); go c.app(r)` ×3 | `sync.join` (`WaitGroupJoin`: three `Add(1)`s, `num_added ≤ 3`) | unchanged | each `app` gets `nodeRunning 1`, `isNode`, the driver state, a third of the network's adder right (§6, Q34), and `ownDone apps P'` with `P' := nodeRunning 1 ∗ njAdder ⅓` |
| `drivers.Add(3)` | a local `join3` lemma over the raw `WaitGroup.Add` spec (three `ownDone`s from one `Add(3)`; `join` has `Add(1)` only) | new (harness-local, glue) | three driver goroutines |
| isolation driver | `time.Sleep`, `atomic.Uint64.Store`, `below` (proved) | unchanged | nothing of raft |
| proposer | `below`, `context.WithTimeout`, **`strconv.Itoa`** (existing axiom, §6 Q33), `node.Propose.spec` (unchanged) with the AU from `tcOpsInv`, `cancel`, `atomic.Int64.Add`, `time.Sleep` | unchanged | `Propose` puts one **normal** entry on `propc` (`propP`'s first disjunct), which the traced `propc` arm needs (`PropAny`) |
| conf-change proposer | `time.Now` (Perennial's trusted spec) and `time.Time.Add` (proved), once before the loop (`concurrent.go:206`); then `atomic.Int64.Load` of `ConfChanges` at a persistent `0` (`Workload`'s `ConfChanges' = 0`: the loop's `&&` short-circuits, so the loop's `time.Now().Before`, `Status` and `ProposeConfChange` are never called) | **corrected** (S1: revision 0 said `time.Now` is never called) | the counter is never written; its points-to is made persistent at allocation |
| `drivers.Wait`, `time.Sleep`, `close(c.stop)` | `join3`, `time.Sleep`, the channel close | unchanged | — |
| `c.apps.Wait()` | `sync.join.WaitGroup.wp_Wait` | unchanged | the three `nodeRunning 1` and the three `njAdder ⅓` back |
| `r.node.Stop()` ×3 | `node.Stop.spec` | unchanged | `nodeRunning 1` in |
| `c.net.Wait()` | `netJoin` (§6, Q34): `njClose` (`njAdder 1` → the wait token), then the raw `Wait` | new (harness-local) | the counter reaches 0 (every network goroutine `Done`) |
| `return c, nil` | `runOver_intro` (`HarnessEnd.lean`) over `startDone`, with the API law `Cluster.traceSim_bootEnd` (A8.4) | the hypothesis `BootEnd D` becomes the law; `runOver_intro` takes `□ [∗list] i ∈ vs, startDone γ i`, `traceDir γd tn`, `Cluster.trace γ = some γd` (S3) | the three `startDone`s, `nodeBoot`, `Cluster.traceSim` |

### 2.3 `app` (one per replica)

| Go | Statement used | Old → new |
|---|---|---|
| `time.NewTicker(c.cfg.Tick)`, `defer ticker.Stop()` | Perennial's `time.NewTicker.spec` (proved; needs `0 < Tick`: Q35) | unchanged |
| `case <-c.stop: return` | the closed-channel receive; `apps.Done` with `nodeRunning 1 ∗ njAdder ⅓` | unchanged |
| `case <-ticker.C: r.node.Tick()` | `node.Tick.spec` (`isNode` only) | unchanged: its traced content is `run`'s `tickc` arm |
| `case rd := <-r.node.Ready()` | `isReadyChan_recvAu.tracedSpec` | **changed** (29n finding 4): `readyGotT`'s last conjunct is the claim `readyToksClaim n γ N ms`, no longer the tokens (§3.1) |
| `c.handleReady(r, rd)` | `raft.IsEmptySnap`, `MemoryStorage.Append`/`SetHardState` (storage contract), `proto.Unmarshal` into a `*ConfChange` (`proto.UnmarshalConfChange.spec`, existing axiom), **`node.ApplyConfChange.spec`** with `confDecided` from `confPolicy_decide` (§2.2), `atomic.Int64.Add` | the snapshot branch refuted from client-visible facts (S12): `readyGot`'s `readyRest` holds `readySnap … L`; at `L = some l` it holds `snapshotCert γ N …`, whence `snapshotCert_made` gives `snapMade γ s` and `snapMade_elem` against `tcSnapsInv`'s `ownSnapsMade γ []` gives `s ∈ []`; at `L = none`, `rd.Snapshot' = null`, so `IsEmptySnap` is true. The `ConfChangeV2` arm: dead (the bootstrap entries are `EntryConfChange`, and no other conf entry is committed, G3). The `CreateSnapshot`/`Compact` branch: `SnapshotEvery = 0` |
| `r.node.Advance()` | **`node.Advance.tracedSpec`** (new, §3.1) | the claim in, `[∗list] q ∈ ms, trTok γ q.st` out. The stopped disjunct is refuted by `nodeRunning_stopped`: the `app` holds `nodeRunning 1` |
| `for _, m := range rd.Messages { c.send(r, proto.Clone(m).(*pb.Message), …) }` | **`proto.ClonePb.spec`** (existing axiom) at rafthttp's `pbMessage` (`PbMessage.lean`, the `PbType` of a `*raftpb.Message`), `below`, `send` (below) | **corrected** (S1): revision 0 said "`proto.Clone` as kvreconf"; kvreconf copies messages by hand (`copyMsg`), and the generic `proto.Clone.spec` has no `Message` case. Glue to check in Probe A: `ClonePb`'s `T.ro l m` from the `Ready`'s `msgOwn q.loc (readyDq q.st) q.st`, and the clone's `T.dec l' m'` with `eqv` into `node.Step`'s `msgPtsC … ⟨st.msg, st.ents, st.snap, st.ctx, []⟩` (the etcd server's `netRecv` does the same from a decoded copy) |

**When the harness sends, checked against the Go.** `app` calls `handleReady`, then `Advance`, then
`send` for each message (`concurrent.go`, the comment at the loop). `node.Advance` returns only once
`run` has taken the `advancec` rendezvous (or is stopped). `run` arms `advancec` only in the `readyc`
arm, after `n.rn.acceptReady(rd)` has returned (`node.go:435-446`), and `acceptReady` ends with
`traceReady`, the `Ready` line that mints the tokens. So every message is handed to the network after
its sender's `Ready` line, and the tokens are there at `Advance`'s return.

### 2.4 `send` (one goroutine per message)

| Go | Statement used | Old → new |
|---|---|---|
| `c.net.Add(1)` (in `app`), `go func(){…}` | `netJoin.wp_Add` (§6, Q34): the caller's `njAdder ⅓` and its thread token in, `njDone` out | new (harness-local) |
| `time.Sleep`, `c.replica(m.GetTo())` (proved), `m.GetType()`, `m.GetTo()`, `isolated.Load` | Perennial, `Cluster.replica.wp_proof`, the message getters | unchanged |
| `dst.node.Step(ctx, m)` | **`node.Step.tracedSpec`**, now a corollary: `stepIn_intro` (with `trTok`) then `node.Step.spec` | statement text unchanged (F2) |
| `if typ == pb.MsgSnap` (twice) | the law **`trTok_type`**, read before `Step` consumes the token: `trTok γ st ⊢ trTok γ st ∗ ⌜Cluster.trace γ ≠ none → st.msg.Type' ≠ MsgSnap⌝` | new law. Both `ReportSnapshot` calls are dead |
| `src.node.ReportUnreachable(to)` | `node.ReportUnreachable.spec` (`isNode` only; it may run after `src` is stopped: `<-n.done`) | unchanged: its traced content is `run`'s `recvc` arm on `UnreachPath` |
| `c.Dropped/Delivered.Add`, `cancel` | Perennial | unchanged |
| `defer c.net.Done()` | `netJoin.wp_Done` (the slot's thread token back) | new |

A dropped or timed-out message's token is discarded (the logic is affine). At most once holds
because the token is consumed by the one `Step` that delivers it.

---

## 3. The node API's traced statements, and the gated `node.run` that proves them

### 3.1 The client statements (`TracedNodeApi.lean`, on `etc/api/raft.txt`)

Design rule (revised, F2/F3): **one proved spec per function**; a gate lives in a sealed predicate
(`stepIn`, `nodeDriver`, `isNode`'s invariants), never as a second triple to keep in step with the
first. Where a traced client needs more than today's post (`Ready`, `Advance`), the traced statement is
a separate, proved triple whose untraced reading is today's; today's spec stays proved for every `γ`,
traced or not, so no existing client changes but §3.5's refusals and F2's `stepIn_intro` premise.

| Function | Old (today) | New |
|---|---|---|
| `StartNode` | `StartNode.gatedSpec` (frozen Draft, over `startTrace`); `StartNode.tracedSpec D` (hypothesis, `D` free) | A8.3: the gated post gains `startDoneB γ cv.ID'`; `StartNode.tracedSpec` has no parameter, its post the sealed `startDone γ cv.ID'`. Proved from `setupNode`'s traced spec (§5) |
| `node.Tick` | `node.Tick.spec` | unchanged |
| `node.Ready` / `isReadyChan_recvAu` | untraced law; `.tracedSpec` (hypothesis) with `readyGotT` = `readyGot` ∗ `[∗list] q ∈ ms, trTok γ q.st` (**unprovable**, 29n finding 4) | `readyGotT` = `readyGot` ∗ **`readyToksClaim n γ N ms`**. `.tracedSpec` a theorem; `isReadyChan_recvAu` stays proved for every `γ` (it drops the claim) |
| `node.Advance` | `node.Advance.spec` (no tokens) | **unchanged text, proved for every `γ`** (F3: `run` needs nothing back). New **`node.Advance.tracedSpec`**: its pre ∗ `readyToksClaim n γ N ms`; post: its first disjunct ∗ `[∗list] q ∈ ms, trTok γ q.st`; the stopped disjunct gives nothing |
| `node.Propose` | `node.Propose.spec` | unchanged (the `propc` payload's entry is normal by construction) |
| `node.ApplyConfChange` | `node.ApplyConfChange.spec` | unchanged (traced content: `run`'s `confc` arm) |
| `node.Step` | `node.Step.spec` (`stepIn`); `.tracedSpec` (hypothesis) | **`node.Step.spec` unchanged, proved for every `γ`** (F2). `stepIn`'s sealed body is gated through `stepP` (§3.2 items 5-6). **`stepIn_intro` gains `trTok γ st`.** `node.Step.tracedSpec` is a corollary. New law `trTok_type` |
| `node.ReportUnreachable` | `node.ReportUnreachable.spec` | unchanged |
| `node.Stop` | `node.Stop.spec` | unchanged |
| `node.ReadIndex`, `.TransferLeadership`, `.ForgetLeader`, `.ReportSnapshot`, `.ProposeConfChange` | no trace premise | **refused at a traced node** (§3.5): each gains `Cluster.trace γ = none →` |

```lean
-- InvNode.lean (moved from TracedNodeApi.lean: `stepIn_intro` is here; its sealed body needs only a
-- private import of `TracedRecvTok`, which `InvNodeChan` already reaches through `InvRawnodeReady`)
@[no_expose] def trTok (γ : Cluster) (st : MsgSt) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(True)
  | some γd => iprop(⌜TrSent st⌝ ∗ recvTokOf γd st.msg st.ents st.ctx)

theorem stepIn_intro (γ : Cluster) (N : Namespace) (id : w64) (ml : Loc) (src : w64) (st : MsgSt) :
    st.msg.To' = id →
    sentMsg (GF := GF) γ N src st ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      msgCredits γ N st ∗ snapLocalMsg γ id st ∗ trTok γ st ⊢        -- new conjunct
    |==> stepIn γ N id ml

/-- The driver's claim on the tokens of a received `Ready`'s messages `ms` (sealed; exclusive).
Untraced `True`. Traced: the driver's element of the node's escrow (`rtkInv`, §3.2 item 2) at the
`Ready`'s key, recording `ms`. **A departure from "no identification handles"** (PRINCIPLES): a
resource every traced driver threads from `Ready` to `Advance`. It carries content (which messages
the tokens are for), and a driver that drops it loses only the tokens, never the node's progress.
Alternative considered: keep `ms` inside the sealed `nodeDriver`, which needs a field of the
client-visible `NodeDriverState` (and `afterReady`'s argument) set by every client. -/
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

**F2's call sites (checked).** `stepIn_intro` is used at four places; each holds
`h : Cluster.trace γ = none` (from `cluster_alloc`, `InvNodeRule.lean:214`) and discharges the new
conjunct by `trTok_untraced γ st h`:
- etcd's server, `InvNet.lean:101` (`stepIn_of_recv`): it opens `srvClusterOk γ.srv`
  (`SrvRaftLog.lean:768`, the last conjunct `⌜Cluster.trace γ.raft.cl = none⌝`); the same `icases`
  names it.
- kvreconf, `Cluster__step.lean:93`: `isClusterC`'s `%Htr0` (`DefsCluster.lean:292`).
- kvdurable, `Cluster__step.lean:90`: `isClusterC`'s `%Htr0` (`kvdurable/Defs.lean:681`).
- kv, `deliver.lean:90`: **not held today**. `deliver.spec` holds `kvPeerOk γ id nd` per peer
  (`kv/Cluster.lean:100`), which carries `⌜γ.snapLoc id = none⌝` but not the trace. kv's own predicate
  `kvPeerOk` gains `⌜Cluster.trace γ = none⌝`, introduced at its one construction
  (`StartCluster.lean:398-401`), where `kvCluster_alloc`'s `%Htr0` is in scope (`StartCluster.lean:296`).
  `deliver.spec`'s text is unchanged; kv's `interface/` changes by `kvPeerOk`'s body.

`node.ProposeConfChange` (`node__ProposeConfChange.lean:116-122`) builds `stepIn` by unfolding it
(not through `stepIn_intro`) for its conf-change `MsgProp`. With `fwdP` gated on normal entries it
cannot do so at a traced node: its refusal premise (§3.5) is what its proof uses. `node.Step.wp_proof`
itself is unchanged: it passes `stepIn`'s `stepP` to `stepWithWaitOption` whatever `stepP` is. The
`RaftWitness` part has its own copy of raft and is not touched.

### 3.2 The gated `node.run`

**`node.run.spec`**. Old: `∀ γ id n, γ.raft.reTrace = none → {{ isPkgInit ∗ isNodeChan γ id n ∗ runPre γ id n }} n.run() {{ True }}`.
**New, at the end of the work** (§9 "Order of work"): the premise dropped, one spec for both modes, the
traced content in the invariants it opens. Until every traced arm is proved, today's statement stays
and the gated one is the separate theorem `node.run.gated_of` (§9). Its `wp_proof` cites the callee
specs it cites today, plus `raft.Step.spec` with the proved `stepBundle_traced` (slice 30c, applied as
`stepBundle_traced.on_of_statement` / `onG_of_statement`), `raft.tickElection.spec`,
`raft.tickHeartbeat.spec`, and the traced RawNode triples of §3.3.

**What the node's invariants gain (sealed, raft-internal; each gate's `none` arm is today's body):**
1. **`ownRawNode`'s traced conjunct** (`rnTrace`, slice 25n) gains:
   - *(a) flag to delivery* (29n finding 2): `rs.delivered ≠ [] → b = true` for the capability's
     `∃ b`. `rnTrace` takes `rs.delivered` (or the clause sits next to it in `ownRawNode`).
   - *(b) the outbox's types* (§3.6, G1): `TrOutTy s` with its scope `s.lt = none` and `ReadIdle s`.
   - *(c) the leader exclusion* (§3.4): `s.role ≠ follower → applied ≥ |γ.reBoot|`.
2. **The node's token escrow** (F3; new, per node). `NodeNames` gains the fields `rtk : GName` (a ghost
   map `Nat ↦ List QMsg`, the `Ready`s' keys), `np : GName` (an exclusive token) and `dep : GName` (a
   monotone count of the keys deposited), allocated in `newNode`/`setupNode` (per node, S12). A new
   invariant, in `isNodeChan` (persistent), gated:
   ```
   rtkInv γn := inv rtkN (∃ (M : GMap Nat (List QMsg)) (a : Nat) (pend : Bool),
     ghostMapAuth γn.rtk 1 M ∗ ⌜dom M = [0, a)⌝ ∗ (if pend then own γn.np (Excl ()) else True) ∗
     monoNatAuth γn.dep (if pend then a - 1 else a) ∗
     [∗map] j ↦ ms ∈ M, ⌜j < (if pend then a - 1 else a)⌝ -∗
        (([∗list] q ∈ ms, readyTok γ q.st) ∨ ghostMapElem γn.rtk j (DFrac.own 1) ms))
   ```
   (`pend`: the last key's tokens not yet deposited; a key below the deposited count stays deposited,
   since the count only grows; `readyTok` is `acceptReady`'s token, whose traced
   body becomes `⌜TrSent q.st⌝ ∗ recvTokOf …`, §3.6.) Traced, `readyToksClaim n γ N ms := ∃ γn j,
   ⌜NodeOk γ γn ∧ γn's node is n⌝ ∗ isNodeChan γn … ∗ ghostMapElem γn.rtk j (DFrac.own 1) ms`.
   `run`'s loop invariant holds `own γn.np (Excl ())` whenever no deposit is pending (idle and busy).
3. **`readyc` commit** (`readyP`, the `readyc` payload): `run` opens `rtkInv`, inserts the fresh key
   `a ↦ ms` (the `Ready`'s handed-out messages), sets `pend := true` by putting `np` in, and puts the
   element `a ↦ ms` (the claim) into `readyP`. **After `acceptReady`** (same arm, before `advancec` is
   armed, `node.go:436-438`): `run` opens `rtkInv` with `acceptReady`'s `"Htoks"`, takes `np` back,
   sets `pend := false`: key `a`'s tokens are now deposited.
4. **`advInv`** (the `advancec` protocol). `run` lends `np` at the rendezvous: `advDep` (run first,
   `RcvPending`) and the `SndPending → RcvCommit` step (driver first) carry it:
   - `RcvPending`: `advDep` gains `own γn.np (Excl ())`; the sender at its commit opens `rtkInv`: `pend`
     is `false` (else two `np`s), so every key in `dom M`, its claim's `j` included, is deposited; it
     swaps its element in and takes the tokens. It leaves `np` in `advRet` for `run`.
   - `SndPending`: the driver's request `γ.req` (fixed name; `AdvReq` gains `Option Nat`) records its
     claim's key `j` (`none` untraced, or for a driver without a claim). `run`, meeting it, holds `np`, so
     opens `rtkInv` (`pend = false`, so the deposited count is `a`), sees `j ∈ dom M = [0, a)`, and puts
     the persistent "key `j` deposited" fact `monoNatLb γn.dep (j + 1)` in the `RcvCommit` answer (with
     the agreeing `req` half); the driver at `RcvCommit → Idle`, or later, opens `rtkInv` and takes the
     tokens with it, whatever `run` has allocated since.
   - A driver without a claim (`node.Advance.spec`) takes nothing: its key's tokens stay in `rtkInv`
     forever. **`run` needs nothing back but `np`, which is its own and which `advRet`/`RcvCommit` give
     back in both orders, whatever the driver holds.** So `node.Advance.spec` is proved for every `γ`.
   - A stale claim (a key `j` from an earlier `Ready` the driver advanced without it) is harmless:
     its key is in `dom M` and deposited, so the traced spec delivers its `ms`.
   - Argument against the Go (`node.go` `run`): `advancec` is set only in `case readyc <- rd:` after
     `n.rn.acceptReady(rd)` returns (`:435-441`, `asyncStorageWrites` false), and the loop head arms
     `readyc` again only when `advancec == nil` (`:354`), i.e. after `case <-advancec:` (`:443-446`). So
     between a key's allocation and its deposit `run` executes no `advancec` case: the rendezvous always
     finds `pend = false`, which `np` makes a logical fact. `Advance()` itself is a send on the
     unbuffered `advancec` or a receive on `done` (stopped: nothing taken, nothing owed).
   - Untraced (`Cluster.trace γ = none`), `rtkInv` is `True` and `np` is not used: today's protocol.
5. **`netP`** (the `recvc` payload), gated:
   - traced, the network disjunct also carries `⌜TrNetTy st.msg.Type'⌝ ∗ recvTokOf γd st.msg st.ents st.ctx`,
     or its type is `MsgUnreachable` (`ReportUnreachable`); the second disjunct `hupP` (`Campaign`) is
     kept;
   - untraced, today's `netP`.
6. **`fwdP`** (a forwarded proposal on `propc`), gated: traced, `∀ e ∈ st.ents, e.Type' = EntryNormal`.

`stepIn` itself is unchanged; `NodeOk γ γn` gives `γn.raft = γ.raft` (`InvApi.lean:1649`), so the
gates read `Cluster.trace γ`. `stepIn_intro`'s proof (`ApiImpl.stepIn_intro_impl`) splits on the trace:
untraced, today's; traced, `trTok`'s `TrSent` sends a `MsgProp` to `fwdP` (normal entries) and the
rest to `netP` with its `TrNetTy` and token.

**Arm by arm** (the `select` in `node.go`'s `run`):

| Arm (Go) | Callee triple | Proved? | Premises from where |
|---|---|---|---|
| loop head: `n.rn.HasReady()`, `n.rn.readyWithoutAccept()` | `HasReady`, `readyWithoutAccept.spec` (one spec for both modes, slice 28n) | yes (re-opened by 1(a)-(c), §3.3) | `ownRawNode` |
| `case pm := <-propc: m.From = r.id; r.Step(m)` | `wp_rn_raft_Step_prop_traced` over `stepBundle_traced.onG PropAny` | yes (25n, 30c; re-opened, §3.3) | `PropAny`: `MsgProp`, non-empty, **normal entries** (`propP`; `fwdP`'s gated clause), `γ.reBoot ≠ []` (`trCapB_reBoot`). The bounds from the ceiling (below) |
| `case m := <-recvc` (guard: response from an unknown `From` → drop; else `r.Step(m)`) | `raft.Step.traced` (`raft.Step.tracedTriple`, slice 30c) | yes (re-opened, §3.3) | the token and `TrNetTy` from `netP` (5.); `StepNodeOk`'s `MsgAppResp` clause from the guard's `Progress` lookup; `MsgUnreachable` at term 0 (`UnreachPath`); `MsgHup` from `hupP`. The rest: §4 |
| `case cc := <-confc: r.applyConfChange(cc)` | traced `raft.applyConfChange` → traced `switchToConfig` | **no** (29n items 1-2) | the capability **booted** by 1(a): `DynCCPre` puts the entry inside the delivered log. `trCapB_hookGate_applyCC` (proved) at a follower; the leader excluded by 1(c) and §3.4 |
| `case <-tickc: n.rn.Tick()` | `RawNode.Tick.traced` (26n) | yes (re-opened, §3.3) | `tickInv`'s credit; the bounds |
| `case readyc <- rd: n.rn.acceptReady(rd)` | `RawNode.acceptReady.spec` (one spec, 28n): fires the `Ready` line, post `[∗list] q ∈ ms, readyTok γ q.st` | yes (re-opened: `readyTok`'s body and 1(a)-(b), §3.3) | `ownRawNodeReady`; the escrow's allocation at the commit and deposit after (2.-3.) |
| `case <-advancec: n.rn.Advance(rd)` | traced `RawNode.Advance`: `stepsOnAdvance`'s self-addressed responses over `raft.Step.traced` with `pendingRel`'s `selfTok` (Q26 (a)); the storage acknowledgements over `stepBundle_traced_storAck` | **no** (designed in 28n, `AckEnd` done in 30c) | the self tokens from `pendingRel`'s `.self` arm; `TrNoSnap` makes the snapshot arm vacuous. The handed-out tokens are already in `rtkInv` (3.) |
| `case c := <-status` | `getStatus` | yes (reads only) | — |
| `case <-stop: close(done)` | the stop protocol | yes | — |

**The bounds premises of the traced triples** (`uint.Z rs.tc + 1 < traceNumBound`, and
`receiptBound GF + γ.reBoot.length ≤ traceNumBound`): the first from `termLB γ.bud rs.tc` and
`budgetInv` (`rs.tc ≤ receiptBound GF`) with the cluster's `readyFits` (`receiptBound GF + 3 ≤ 2^61`);
the second is `readyFits` itself (`γ.reBoot.length = 3`). Read once per arm; no new invariant.

### 3.3 The RawNode triples `run` uses, and what revision 1 re-opens (S5)

- **Proved, re-opened by `rnTrace`'s new clauses 1(a)-(c)** (each re-establishes `ownRawNode` at a new
  state, so each proof re-establishes the clauses; their statements do not change):
  - `RawNode.Tick.traced` (26n): (a) `delivered` unchanged; (b) via its `raft.Step.traced`; (c) a
    campaign through `hup` (`HupCampaigns`' `¬ hasUnappliedConfChanges`, with §3.4's lemma (i)).
  - `RawNode.acceptReady.spec` (28n): (a) established here (the `Ready` line sets the flag before
    `delivered` grows); (b) the outbox emptied; its post's `readyTok` body changes (§3.6), so it is
    re-opened for that too.
  - `RawNode.readyWithoutAccept.spec` (28n): reads only; frames the clauses.
  - `wp_rn_raft_Step_prop_traced` (25n) and the `raft.Step.traced` assembly (30c): (b) is L1's
    obligation; (a) frame; (c) `hup` as for `Tick`.
  - `stepBundle_traced_storAck` (30c), `stepBundle_traced_unreach` (27n): through the assembly.
- **Proved, unchanged:** `trCapB_hookGate_applyCC`, `traceConfChangeEvent.tracedSpec_proof` (29n).
- `RawNode.Step.traced`, `RawNode.Ready.traced`, `RawNode.ReportUnreachable.traced` exist but are not on
  `run`'s path (`run` calls `r.Step` and `acceptReady` directly); models for the `recvc` arm.
- **Not yet:** the traced `RawNode.Advance` (28n's design); the traced `raft.applyConfChange`,
  `raft.switchToConfig`, `RawNode.ApplyConfChange` (29n items 1-2); the traced `newRaft`,
  `NewRawNode`, `Bootstrap`, `setupNode` (§5).
- The alternative S5 offered (keep a clause only `run` reads in `run`'s own invariants) does not apply:
  1(a) needs the capability's flag, which only `rnTrace` sees; 1(b) and 1(c) change inside
  `raft.Step`. So the clauses go into `rnTrace` and the re-openings above are the cost.

### 3.4 `switchToConfig`: the read-only lending, the leader case

- **Read-only lending** (29n finding 1, (a)): `traceEvent.spec` takes `RaftReadLend` (the hard state's
  fields, `raftLog`'s `lastIndex`, `state`, `id`, the tracker's `Config.Voters` maps; no `Progress`) in
  place of `RaftLend`. `raftLend_self` gives it from the whole struct; the `Changer` specs give back the
  old configuration's maps, only read (`Config.Clone`); `switchToConfig` lends them from its open
  struct. `traceConfChangeEvent.spec` becomes one spec over `RaftReadLend`; its callers are
  `switchToConfig` and `newRaft`'s call (A7).
- **The leader case** (29n finding 3; restated, S6). `AccIdle` (`TraceSimMatch.lean:4437`) says: no
  outgoing configuration, `commit ≤ |log|`, no pending conf change, the last committed conf entry is
  the configuration. It says nothing of the role. The obstacle at a leader is elsewhere: there
  `switchToConfig` (`raft.go:2015-2028`) also logs the `Commit` line through `maybeCommit` and sends
  through `bcastAppend`/`maybeSendAppend`, which `trCapB_hookGate_applyCC` (needing the phase `SimIdle`,
  `TracedApplyCC.lean:174`) covers neither. **Excluded instead of proved**, by:
  1. `raft.hup` refuses to campaign while `hasUnappliedConfChanges()` (`raft.go:1001`), and every way
     out of the follower role goes through `hup` at a traced node (`prevote = false`; `MsgTimeoutNow`
     needs a transfer, refused). `hasUnappliedConfChanges` is false iff `applied ≥ committed` or no
     conf entry in `(applied, committed]` (`raft.go:1013-1038`).
  2. **Lemma (i), the bootstrap log prefix** (S7): at a traced node, `committed ≥ |γ.reBoot|` and the
     log's entries `1..|γ.reBoot|` are the bootstrap conf entries. Source: `Bootstrap` appends `boot` and
     commits it (A7's positions `k + 4`), `committed` is monotone, and the committed log's prefix is
     `boot` (`isCommittedLogLb γ boot`, `cluster_alloc`'s) with `ownRawNode`'s log agreeing with the
     committed log below `committed`. With 1, a campaign happens only at `applied ≥ |γ.reBoot|`:
     otherwise entry `applied + 1 ≤ |γ.reBoot| ≤ committed` is a conf entry. `applied` is monotone, so
     clause 1(c) `role ≠ follower → applied ≥ |γ.reBoot|` holds from then on.
  3. **Lemma (ii), the `confc` arm** (S7): an entry `node.ApplyConfChange.spec` admits (`l[k]? = some
     e`, `e.isConfChange`, `v.applied ≤ k`, `confDecided γ k`) has `k + 1 > raftLog.applied`. Source: A1
     at `Advance` (`advanceP`'s `undecFree … ca` with `monoNatLbOwn γ.cam ca`): the driver applies a
     `Ready`'s conf entries before its `Advance`, and `raftLog.applied` moves only at `Advance`
     (`MsgStorageApplyResp`, `rawnode.go`'s `acceptApplying`/`appliedTo`) past entries the driver's
     view `v.applied` has passed; `undecFree` says no undecided conf entry was skipped below `ca`.
     **To be read against `undecFree`/`cam`**: the step "the entry at `k` is undecided at the last
     `Advance`, so `k ≥ applied`" is the one unchecked link.
  4. **Lemma (iii), G3 (found in this revision): no conf entry past `|γ.reBoot|` at a traced cluster.**
     Needed because (ii) and 1(c) give `k + 1 > applied ≥ |γ.reBoot|` at a non-follower, and only G3
     turns that into a contradiction. Source to argue: entries enter a log only by `Bootstrap` (`boot`),
     a leader's append of a proposal's entries (`propP`: `propEntryM d`, normal; `fwdP`'s gated clause;
     `ProposeConfChange` refused) and `becomeLeader`'s empty normal entry. Whether raft's ghost state
     already carries an origin invariant on log entries (the entry tickets `entTk`) that a gate can
     strengthen to "normal past `boot`" is **not checked**; flagged in L2.
  5. From 1-4, the node is a follower at the `confc` arm, so `AccIdle` and `SimIdle` apply.

  If (ii) or G3 fails, the fallback is 29n's: a line lemma for `ApplyConfChange` at a leader under the
  corrected specification (with its `Commit` and send lines). That lemma is not argued here.

### 3.5 The calls refused at a traced node

`run`'s `recvc` and `propc` arms can only step what the traced bundle covers (`StepEndTy ∨ AckTy`).
At a traced node the following arrive through those arms and are covered by no path: `MsgReadIndex`
(`ReadIndex`), `MsgTransferLeader` (`TransferLeadership`), `MsgForgetLeader` (`ForgetLeader`),
`MsgSnapStatus` (`ReportSnapshot`), a conf-change `MsgProp` (`ProposeConfChange`).

Each of these five `node.X.spec`s gains the premise `Cluster.trace γ = none`, and `netP`'s traced local
disjunct is restricted (§3.2, 5.). None is called by the harness (`ReportSnapshot`'s calls are dead by
`trTok_type`; the premise stays because another client of a traced cluster could call it, and `run`
could not step its `MsgSnapStatus`). `ProposeConfChange`'s premise is used by its own proof (§3.1).
Cost: L3. Rejected: bundle paths for these types (a transfer is not modelled as one; a conf change is
outside the workload; the other three would each need a `StepEnd` clause for no harness use).

### 3.6 The messages' types at the receiver (G1, G2)

`raft.Step.tracedTriple` needs `StepEndTy m.Type' ∨ AckTy m.Type'`, and the `propc` arm needs a
proposal's entries normal. At the `recvc` arm `netP` gives only `netStepTypes`; `fwdP` gives no entry
types. **No statement today supplies either fact.** The design:

- `TrSent st := TrNetTy st.msg.Type' ∨ (st.msg.Type' = MsgProp ∧ ∀ e ∈ st.ents, e.Type' = EntryNormal)`.
- **At the sender**: `rnTrace` keeps `TrOutTy s` with its scope `s.lt = none ∧ ReadIdle s` (§3.2,
  1(b)); `acceptReady`'s tokens `readyTok γ q.st` become `⌜TrSent q.st⌝ ∗ recvTokOf …`
  (`outboxRelP` relates `q.st` to an outbox message, so `TrOutTy` gives `TrSent`); they go through
  `rtkInv` to the driver as `trTok` (same body).
- **Through the client**: `stepIn_intro` takes `trTok` (with `TrSent`) into the gated `stepP`: a
  `MsgProp` to `fwdP` (normal entries), anything else to `netP` (`TrNetTy` with the token).
- **Kept by**: every traced triple on `run`'s path. The handed-out messages are `r.msgs` and the
  `msgsAfterAppend` not to self (`rawnode.go:145`, `:179-183`; the self ones go to `stepsOnAdvance`,
  `:414-417`). Their types at a traced node: `MsgApp`, `MsgHeartbeat` (leader), `MsgVote` (candidate),
  the three responses (`TrNetTy`), and a follower's forwarded `MsgProp` (normal entries, by `PropAny`).
  Excluded: `MsgReadIndexResp` (only from a pending read: `ReadIdle`), `MsgTimeoutNow` (`lt ≠ none`),
  `MsgSnap` (`maybeSendSnapshot` only after compaction: `TrNoSnap`, L5), pre-votes (`prevote = false`),
  forwarded `MsgReadIndex`/`MsgTransferLeader` (only from stepping those types, which `StepEndTy`
  excludes), storage messages (`AsyncStorageWrites = false`: `:163-173` not taken). `ReadIdle` and
  `lt = none` are kept: only `MsgReadIndex` adds a read and only `MsgTransferLeader` sets `lt`, both
  excluded; `becomeX` resets `lt`.
- **Where the obligation lands**: `raft.Step.tracedTriple`'s post must say it: either a new conjunct
  `OutTyStep s s'` (re-opening slice 30c's assembly, one conjunct per path), or a derivation from
  `raft.Step.spec`'s `LeaderNonpropResultC` and the role results if they pin the queued types. L1.

### 3.7 The booted flag (29n finding 2)

The capability's flag `b` (under `∃ b` in `rnTrace`): `StartNode` returns it unset; the `Ready` line
(`trCap_fire_ready`), a receive line (`trCap_fire_recv`) and a `BecomeCandidate` (`trCap_fire_any`)
set it. `acceptReady` is the only function that moves `rs.delivered`, and it fires the `Ready` line
before returning, so clause 1(a) is established there and kept by everything else (flags only go up).
The `confc` arm reads it. Q19 (a) lets the bundle and the ticks run at either flag.

---

## 4. `stepBundle_traced.statement`'s premises (slice 30c's list) and where `run` gets each

`run` calls `raft.Step.traced` from the `recvc` and `propc` arms, from `RawNode.Tick.traced`
(`MsgHup`, `MsgBeat`), and from the traced `RawNode.Advance` (self responses, acknowledgements).

| Premise | Discharged by | From where |
|---|---|---|
| `s.gh.tr = some γd` | `ownRawNode`'s trace field at a traced cluster | `cluster_alloc_traced` → `StartNode` |
| `s.prevote = false`, `s.cq = false` | `rnTrace`'s scope; `r.[raft,"checkQuorum"] ↦□ false` with `ownRaftPhysC_cq` | `startTrace`'s `TracedConfigOk` |
| `StepEndTy m.Type' ∨ AckTy m.Type'` | `recvc`: `netP`'s gated `TrNetTy` (§3.6) or `MsgUnreachable`/`MsgHup`; `propc`: `MsgProp`; ticks: `MsgHup`/`MsgBeat`; `Advance`: self responses (`TrNetTy`) or `AckTy` | **G1** for the network case |
| `NStateWf s` | `ownRawNode`'s `%Hwf` | — |
| local types at term 0 | the messages' constructors (`hupSt`, `propMsgM`, `ReportUnreachable`'s literal, raft's `tick*`, `newStorageApplyRespMsg`) | — |
| `MsgStorageAppendResp → Term ≤ s.term` | `raft.Step.spec`'s own premise, which `RawNode.Advance` supplies | — |
| a traced message to `id` | `NetMsgOk`'s `To = id` | `netP` |
| `s.term + 1`, `m.Term` below `traceNumBound` | the ceiling `rs.tc` (`RNPv`), bounded by the budget (§3.2); the message's by `termLB` in `netP` | `budgetInv` |
| `MsgTrOk` | `isRaftMsg_trRecv` (via `netP`'s `isMessage`/`isMessageC`) | the sender's `isRaftMsg` |
| the receipts' fit | the cluster's `readyFits` | `cluster_alloc_traced` |
| no learners | `rnTrace`'s scope (`c.learners = ∅`) | `startTrace` |
| `domSet s.progress ⊆ voters ∪ learners` | `ownRaftPhysC_dom` | — |
| not a pre-candidate | `ownRaftPhysC_precand` with `prevote = false` | — |
| `TrRecvShape` | `isRaftMsg_trRecv` (`SentMsgShape`, `Msg.TrOk`'s heartbeat clauses, Q18/Q28 (c)) | the sender's `isRaftMsg` |
| a proposal's batch non-empty, of normal entries | `propP` (one normal entry); `fwdP`'s gated clause | **G2** for the forwarded case |
| `StepNodeOk`: `PrvalsOk s`, `domSet s.prvals = domSet s.progress` | `ownRaftPhysC_prvals_ok`, `ownTrackerC_prvals_dom` | — |
| `StepNodeOk`: `MsgAppResp → m.From' ∈ domSet s.progress` | `recvc`'s guard (`r.trk.Progress[m.From] == nil` → drop), read with `ownTrackerC_progress_map` | — |
| the recv token `recvTokOf` | `netP`'s gated token (from `stepIn_intro`'s `trTok`); self responses: `pendingRel`'s `selfTok` | the sender's `acceptReady`, through `rtkInv` and the driver |
| (`raft.Step.tracedTriple`) `MsgStorageAppendResp → sn = none`; `MsgStorageApplyResp → ents ≠ [] → c.autoLeave = false` | no snapshot (`TrNoSnap`, L5); no joint configuration at a traced node (bootstrap `AddNode`s only, G3) | — |

Every row but G1, G2 (and G3, L5 behind two of them) cites a fact that exists today.

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

All are logged while unbooted, through `trCap_fire_boot` (premise `BootNext C id o e`, A7). The
segments clause `BootSegs C L` in `simInv` is kept (A7, proved).

### 5.2 The traced constructors (not yet; statements to write; S4)

Notation: `cC` is the voters' configuration (`(elements cC.incoming).Perm vs`, `cC.outgoing = ∅`), what
the capability is stated at; raft's own configuration `c` is empty at positions 0-2 and grows at
positions `k + 4`; `raft.becomeFollower.traced` keeps them apart (`hcC : b = true → cC = c`,
`TracedHooks.lean:417-421`). The phase `Φvs C _ _ := C = vs` fixes the capability's `C` to the caller's
voters (`startTrace_trCapB` needs `Φ vs …` initially; `tn.voters = vs`).

- **`newRaft.tracedSpec`** (`newRaft.spec` today sets `tr := none`):
  - pre: `newRaft.spec`'s pre with `startTrace γ vs cv` and `nodeBoot γ N vs ctxs cv.ID'`;
  - post: `ownRaftPhys` at raft's `c` with `s.gh.tr = some γd`, and
    `trCapB (some γd) γ.raftNames r cv.ID' cC false Φvs Λ2` with
    `Λ2 o := ∃ x, o = some x ∧ BootEvAt vs cv.ID' 2 x`;
  - untraced: today's spec.
  - Proved from `startTrace_trCapB` (A4, proved, at `cC` with `Λ := fun o => o = none`) and the gates:
    `trCapB_hookGate_init` gives position 0; `traceConfChangeEvent.spec` over `RaftReadLend` with
    `trCapB_hookGate_ccBoot` gives 1; `raft.becomeFollower.traced` at `b = false` gives 2. Each gate's
    `BootNext vs id o e` premise comes from the previous `Λ` and `Φvs` (which puts `C = vs`).
- **`RawNode.Bootstrap`'s traced spec**:
  - pre: the capability unbooted at `cC`, `Φvs`, `Λ2`; `bootMarshal` (Q32);
  - post: unbooted at `Λend o := ∃ x, o = some x ∧ BootEvAt vs id (vs.length + 3) x`.
  - Proved from `raft.becomeFollower.traced` (3) and, per peer, the traced `raft.applyConfChange` →
    `switchToConfig` at a follower (`trCapB_hookGate_ccBoot`, positions `k + 4`). No leader case.
- **`NewRawNode`/`setupNode` traced**: thread these. After `Bootstrap`, `simIdle_boot` (slice 21)
  gives the phase `SimIdle C s`. `setupNode` mints `bootDone tn id` by `trCapB_bootDone` (A8.2) at
  `Λend`: its `hΛ` holds since `Φvs C _ _` gives `C = vs`, so `Λend o` is `BootEvAt C id (C.length + 3)`.
  It then packs `rnTrace` (weakening `Λend` to the default `Λ`, the phase `Φvs` to `SimIdle`), with
  `TrNoSnap` from the storage's gated `storBnd` (L5), and allocates the node's escrow `rtkInv` (§3.2, 2.).
- **`StartNode.gatedSpec`** (A8.3) from `setupNode` and `run`'s spawn (`node.run` at a traced node: §9's
  order, `node.run.gated_of` then the dropped premise).

### 5.3 Amendment A8 (Q36 (a), Q37 (a), decided by the coordinator): exact statements

**A8.1: `simInit` (Q36 (a)).** File `TraceSimGhost.lean` (frozen Draft).
- Old: `simInit C := { server := srv, s := fun _ => { v with durable := Etcdraft.durableOf v }, messages := [], pendingMessages := [], reconfigCount := 0 }`.
- **New**: `s := fun i => if i ∈ srv then { v with durable := Etcdraft.durableOf v } else bootJunk`.
  `bootJunk` moves from `TraceSimEnd.lean` to `TraceSimGhost.lean`, above `simInit`; body unchanged.
- Consequences:
  - `bootInit C` equals `simInit C` **propositionally** (function extensionality and an `if` over the
    same test; S12): keep `bootInit` with the lemma `bootInit_eq : bootInit C = simInit C`;
    `newTrace_bootInit`'s conclusion is rewritten by it to `t.init = simInit C`.
  - **Delete** `bootInit_ne_simInit` and `not_bootFacts` (`MainSim.lean`): they become false.
  - New lemma `simInit_s_voter : idAbs i ∈ confAbs C → (simInit C).s (idAbs i) = { v with durable := … }`.
    The users that read a voter's server rewrite by it: `simFx_simInit`, `specInv_simInit`,
    `cfgFixed_simInit`, `startTrace`'s `(simInit vs).s (idAbs cv.ID')`, `voterStart`.
  - `SimRun`'s meaning changes only at non-servers.
- Argument: every reader of `simInit` reads voters' servers only (A7's check); `bootJunk` is a
  follower, so a non-server reader sees a follower too.

**A8.2: the completion witness (Q37 (a)).** Files `TraceSimGhost.lean`, `TracedCap.lean` (frozen).
- `structure TraceNames`: old fields `tr st bag voters bt`. **New**: also `dn : GName`.
  `traceNames_countable` gains the component.
- `def bootDone (tn : TraceNames) (i : w64) : IProp GF := ghostMapElem tn.dn i DfracDiscarded ()`,
  `instance : Persistent (bootDone tn i)`.
- `simInv C tn Fx`: **new** `∃ Dn : GMap w64 Unit` with `ghostMapAuth tn.dn 1 Dn` and
  `(∀ i, Dn !! i = some () → BootDone C L i)`. Everything else unchanged.
- New pure lemma `bootDone_snoc : BootSegs C (L ++ [e]) → BootDone C L i → BootDone C (L ++ [e]) i`
  (if `e` extended `i`'s segment, its length would be `|C| + 5`, and `BootSegs` would need
  `BootEvAt C i (|C| + 4)`, which requires `|C| < |C|`).
- **Every law that closes `simInv`** (found by `iunfold simInv`, S11): the fire laws
  `trCap_fire`, `_ready`, `_recv`, `_boot`, `_bf`, `_booted` (`TracedHooksGlobal.lean`; `_any` and the
  derived variants go through them) use `bootDone_snoc` (they already prove `BootSegs` at `L ++ [e]`);
  `trCapB_perm` (`TracedFamilies.lean:188-208`) keeps `L`, so `Dn`'s clause carries unchanged;
  `Cluster.traceSimInv_alloc` (`TracedApiDraft.lean:161`) gives `Dn = ∅`; the readers `simInv_end`,
  `simInv_end_boot` (`TraceSimEnd.lean`) drop the conjunct (and `simInv_end_boot`'s users read it, A8.4).
- Position uniqueness: the existing **`bootEvAt_unique`** (`TraceSimBootSeg.lean:218`:
  `BootEvAt C i k x → BootEvAt C i k' x → k = k'`); no new lemma (S2).
- **New law** (in `TracedCap.lean`, beside `trCap_fire_boot`):
  ```lean
  theorem trCapB_bootDone (γd) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
      (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) (E : CoPset)
      (hE : ↑(simNS γ) ⊆ E)
      (hΛ : ∀ C cs P o, Φ C cs P → Λ o → ∃ x, o = some x ∧ BootEvAt C id (C.length + 3) x) :
      trCapB (some γd) γ r id c false Φ Λ ={E}=∗
        trCapB (some γd) γ r id c false Φ Λ ∗ ∃ tn, traceDir γd tn ∗ bootDone tn id
  ```
  Argument: open `simInv`. The flag is `false`, so `booted L (idAbs id) = false`: every event of `id`
  is bootstrap-named, its segment is all of them, and `LastOf` makes `o` its last. `BootSegs` puts the
  last at position `len − 1`, and `hΛ` at `|C| + 3`; by `bootEvAt_unique`, `len = |C| + 4`, which is
  `BootDone`. Insert `id` into `Dn` and persist the element.
- `Cluster.traceSimInv_alloc` and `Cluster.traceSim_alloc` gain the resource
  `ghostMapAuth tn.dn 1 (∅ : GMap w64 Unit)`; `traceNames_alloc` allocates it.

**A8.3: `StartNode` returns the witness.**
- `TracedApiDraft.lean`: `def startDoneB (γ : Cluster) (id : w64) : IProp GF := match Cluster.trace γ with | none => True | some γd => ∃ tn, traceDir γd tn ∗ bootDone tn id`.
- `StartNode.gatedSpec`'s post. Old ends with `peers ↦*{dq} pv`. **New**: `… ∗ peers ↦*{dq} pv ∗ startDoneB γ cv.ID'`.
- `TracedNodeApi.lean`: `StartNode.tracedSpec D` → `StartNode.tracedSpec`, post `startDone γ cv.ID'`,
  **`@[no_expose]`**, its body `startDoneB`'s; `StartNode.tracedSpec_of_gated` loses its parameter;
  `startDone` loses `D`. Persistent (instance).

**A8.4: the end law** (`TracedNodeApi.lean`, an API law; replaces the hypothesis `BootEnd D`; stated
over what the client holds, S3):
```lean
theorem Cluster.traceSim_bootEnd (γ : Cluster) (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (id : w64) (γd : GName) (tn : TraceNames) (L : List TraceEv) (E : CoPset) (hE : ↑N ⊆ E)
    (htr : Cluster.trace γ = some γd) (hne : vs ≠ []) (hlen : vs.length < 2 ^ 40) :
    (nodeBoot γ N vs ctxs id ∗ traceDir γd tn ∗ Cluster.traceSim γ vs tn ∗
        □ ([∗list] i ∈ vs, startDone γ i) ∗ traceAuth tn.tr L : IProp GF) ={E}=∗
      traceAuth tn.tr L ∗ ⌜∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.init = simInit vs ∧
        t.server = confAbs vs ∧ t.initSrv = confAbs vs⌝
```
Proved by unsealing `startDone` inside raft (`traceDir_agree` makes each `startDone`'s `tn` the
given one), opening `simInv`: each `bootDone tn i` is in `Dn`, so `BootDone vs L i`; with `SimRun`,
`SimEvents` and `BootSegs`, `newTrace_bootInit` and `bootInit_eq` give the result, which is
`TraceCheck.BootFacts vs L`'s body. `HarnessEnd.lean`: `BootEnd D` is deleted; `runOk_at_end` and
`runOver_intro` take `γd`, `htr`, `traceDir γd tn` and `□ [∗list] i ∈ vs, startDone γ i` in place of
`D`/`HD`/`□ [∗list] i ∈ vs, D tn i`, and `hne`/`hlen`, which the harness has (`vs = [1,2,3]`).

No change to `trCap_fire_boot`, `BootSegs`, `BootNext`, `trCapB`, or any other law's statement (their
proofs add one conjunct each). A8 needs its own review round and re-freeze (`trace-check-frozen-a8`).

---

## 6. Q33, Q34, Q35, and what the closed theorem rests on

**Q33 (`strconv.Itoa`).** Perennial translates `strconv` with bodies only for `ParseUint` and its
errors; `Itoa` is names-only. This repository already has `Spec/strconv/Itoa.lean` and
`axiom strconv.Itoa.wp_proof` (`Proof/strconv/Itoa.lean`, in `etc/tcb-baseline.txt`, K4's), and raft's
own linked results already rest on it (`etc/tcb-collections/raft.txt`). The proposer uses it.
`notes/perennial-changes.md`'s "Workaround here: none yet" is stale; the proposed Perennial change
(translate `Itoa`/`FormatInt` and prove the spec) stands.

**What the closed theorem rests on once `RunConcurrent` is proved** (S1; all existing; none new):
- **Raft's node API path**: the baseline of `etc/tcb-collections/raft.txt`, fifteen axioms of this
  repository: `DescribeConfChange.wp_proof`, `ccDecodeV2_nil`, `fmt.Errorf.wp_proof`,
  `proto.CloneConfState.wp_proof`, `proto.CloneEntry.wp_proof`, `proto.CloneSnapshot.wp_proof`,
  `proto.EqualConfState.wp_proof`, `proto.MarshalConfChange.wp_proof`,
  `proto.MarshalConfChangeV2.wp_proof`, `proto.SizeEntry.wp_proof`, `proto.UnmarshalConfChange.wp_proof`,
  `proto.UnmarshalConfChangeV2.wp_proof`, `raftpb.ConfChangeType.String.wp_proof`,
  `strconv.FormatUint.wp_proof`, `strconv.Itoa.wp_proof` (kv's, kvreconf's and kvdurable's collections
  have the same fifteen). It is an upper bound: the node functions the harness reaches may rest on
  fewer; the collection's `--check --update` after the proof records the exact set.
- **The harness's own calls**: `proto.ClonePb.wp_proof` (`proto.Clone` of a message, at rafthttp's
  `pbMessage`, whose decoder `msgDecode` is an `opaque`, not an axiom); `proto.UnmarshalConfChange.wp_proof`
  and `strconv.Itoa.wp_proof` (already above).
- **Perennial's trusted specs**: `time.Now.wp_proof` (`Perennial/Proof/time/Now.lean:24`); not a line of a
  collection's baseline (they list this repository's axioms), but in `#print axioms`, as for
  `etcd_putget_safe`. `time.NewTicker`, `Sleep`, `Time.Add`, `context.WithTimeout` are proved in Perennial.
- **The package initializers' trust-boundary axioms** (`Init.lean`, generated), as today's
  `raft_tracecheck_safe_of`.

So the tracecheck collection's baseline gains about sixteen `axiom` lines when `RunConcurrent` is
proved: an update of the collection, recorded then, not a trust-base change (each is in
`etc/tcb-baseline.txt` today).

**Q34 (the network's wait group: several adders, unbounded).** A harness-local idiom over the raw
`WaitGroup` specs, backed by thread tokens (CLAUDE.md "Bounds"; Perennial's `tokJoin` is the model).
File `Proof/.../tracecheck/NetJoin.lean`, under `[ThreadBoundLe GF (2 ^ 31)]`.
- **Names**: `γ.wg : WaitGroupNames`, `γ.dep` (the slots' token count), `γ.ad` (the adders' fraction).
- **Invariant**: `njInv γ := ∃ ctr j, ownWaitGroup γ.wg ctr ∗ threadToks j ∗ ownTokAuth γ.dep j ∗ ⌜sint.Z ctr = j⌝ ∗ (ownWaitGroupWaiters γ.wg 0 ∨ dghostVar γ.ad (DFrac.own 1) ())`.
  `isNetJoin N wg γ := isWaitGroup wg γ.wg (N.@"wg") ∗ inv (N.@"inv") (njInv γ)` (**no pure bound**:
  revision 0 carried `⌜threadBound GF ≤ 2^31⌝`; the instance replaces it).
- **Rights**: `njAdder q := dghostVar γ.ad (DFrac.own q) () ∗ isNetJoin` (fractional). `njDone := ownToks γ.dep 1 ∗ isNetJoin`.
- **Laws**: `nj_init` (from a fresh wait group, `njAdder 1`); `njAdder_split`;
  `netJoin.wp_Add : {njAdder q ∗ threadTok} wg.Add(1) {njAdder q ∗ njDone}` (open `njInv` at `⊤`; an
  adder with `q > 0` refutes the right disjunct, so `ownWaitGroupWaiters 0` is there for `Add`'s
  `oldc = 0` case and goes back; the token is deposited, `ctr + 1 = j + 1`);
  `netJoin.wp_Done : {njDone} wg.Done() {threadTok}`; `njClose : njAdder 1 ={⊤}=∗ ownWaitGroupWaiters γ.wg 0`;
  `netJoin.wp_Wait` (by `alloc_wait_token` then the raw `Wait`, as `tokJoin.WaitGroup.wp_Wait_of`).
- **Thread tokens**: `app` deposits one at each `Add`; the `go` gives the parent a fresh one
  (`wp_fork_tok_self`).
- `etc/bounds-allow.txt` lists the idiom's own matches (it is the owner).
- **Perennial**: the general shared-adder join is recorded in `notes/perennial-changes.md` (S7 part 2).
- The same file gives `join3` for `drivers.Add(3)` (three `ownDone`s from one raw `Add(3)` with
  `oldc = 0`; the `WaitGroupJoin` argument at delta 3).

**The thread bound, end to end (F1, checked).**
1. `init_adequate` (`etcdstart/Adequacy.lean:111-119`) runs `goose_adequacy (n + 1) (n + 2)`, so the
   hypothesis of `Hprog` gives `HN : receiptBound GF = n + 1` and `HT : threadBound GF = n + 2`.
2. `tracecheck_adequate_of` with `Hn : n + 2 ≤ 2^31`: `ThreadBoundLe tcGF (2^31)` from `HT` and `Hn`
   (`ThreadBoundLe.of_eq`, `weaken`, `Perennial/ProgramLogic/Bounds.lean`); `receiptBound tcGF + 3 =
   n + 4 ≤ 2^31 + 2 ≤ 2^61` from `HN`.
3. `Main.spec` and `RunConcurrent.spec` take the instance; the corollary (§1.3) takes it directly.
4. `netJoin.wp_Add`: the adder holds `threadTok` and the invariant `threadToks j`, so
   `threadToks_add_one_lt` (`Perennial/GooseLang/Threads.lean:433`) gives `j + 1 < threadBound GF ≤ 2^31`
   (`ThreadBoundLe.le`). `WaitGroup.Add.spec` (`Perennial/Spec/sync/WaitGroup__Add.lean`) needs
   `0 ≤ sint.Z oldc + sint.Z (W32 1) < 2^31` with `oldc` the `w32` counter, `sint.Z oldc = j`
   (representable: `0 ≤ j < 2^31`): `0 ≤ j + 1 < 2^31`. Holds.
5. `join3` and `apps` (`WaitGroupJoin`) add constants (3), within the same bound.

**Q35 (`Workload`'s `Tick > 0`).** Taken, (a): §2.1. Not in the closed statement (§1.3 is at
`defaultCConfig`).

---

## 7. The chain, every statement: proved from, and why that suffices

★ = not proved today. † = flagged in §9. "Re-opened" = proved today, its statement unchanged, its proof
redone for a changed sealed body (§3.3).

| Statement | Proved from (callee statements) | Why it suffices |
|---|---|---|
| `raft_tracecheck_safe` (§1.2) | `tracecheck_adequate_of` (new binders; `Hn : n + 2 ≤ 2^31`), `tcMainSpec` | adequacy turns `Main`'s spec at every `HeapGS` into the operational statement; the instance and `Hbound` from `HT`/`HN` (§6); `Hprem` at each `hG`, as putget |
| `raft_tracecheck_accepts` (§1.3) | `RunConcurrent.spec` at `defaultCConfig` (`Workload` by `decide`) under the instance, `tracecheck_Events_traceAccepts` | the post `runOver c` is the latter's precondition |
| `tcMainSpec` / `Main.spec` ★(premises) | `Main.wp_proof` (proved) with `RunConcurrent.spec` and the checker's Link | unchanged proof, plus passing the instance and `premises boot` |
| `RunConcurrent.spec` ★ | §2.2's calls: `harness_alloc`, `tcOpsInv`/`confPolicy_alloc`/`tcSnapsInv`, `startTraceC_intro`, `StartNode.tracedSpec`, `sync.join`, `join3`, `netJoin`, `app`/`send`, `node.Stop.spec`, `time.Now`, `Time.Add`, `runOver_intro` with `Cluster.traceSim_bootEnd` | allocation gives each voter's `startTraceC`; the three `startDone`s with `traceDir` and `Cluster.traceSim` give `BootFacts`; `runOver_intro` composes |
| `app` ★ (harness-local: `isNode`, driver state, `nodeRunning 1`, `njAdder ⅓`, `ownDone apps …`) | `time.NewTicker`, `node.Tick.spec`, `isReadyChan_recvAu.tracedSpec`, `handleReady`, `node.Advance.tracedSpec`, `proto.ClonePb.spec` at `pbMessage`, `send` | loop invariant: the driver idle, `nodeRunning 1`, `njAdder ⅓`. Each round: the claim at the receive, the tokens at `Advance`, one `send` per token |
| `handleReady` ★ | storage contract, `proto.UnmarshalConfChange.spec`, `confPolicy_decide`, `node.ApplyConfChange.spec`, `snapshotCert_made`, `snapMade_elem` with `tcSnapsInv` | as kv's handler; the snapshot branch refuted from `readySnap` (§2.3) |
| `send` ★ | `netJoin.wp_Add`, `trTok_type`, `node.Step.tracedSpec`, `node.ReportUnreachable.spec`, `netJoin.wp_Done` | the token rides into the goroutine; `ReportSnapshot` dead by `trTok_type` |
| `netJoin` laws, `join3` ★ | raw `WaitGroup.Add/Done/Wait`, `alloc_wait_token`, `threadToks_add_one_lt`, `ThreadBoundLe.le` | §6, end to end |
| `StartNode.tracedSpec` ★ (A8.3) | `StartNode.gatedSpec` (Draft, amended), `startTraceC_eq` | the Draft's over the sealed names (as today's `tracedSpec_of_gated`) |
| `StartNode.gatedSpec` ★ | `setupNode` traced, `node.run.gated_of` then `node.run.spec` (§9's order) | `setupNode` returns the node with `bootDone`, `rtkInv` and `runPre`; `go n.run()` |
| `setupNode`/`NewRawNode` traced ★ | `newRaft.tracedSpec`, `RawNode.Bootstrap` traced, `trCapB_bootDone`, `simIdle_boot`, the gated `storBnd` († L5) | §5.2 |
| `newRaft.tracedSpec` ★ | `startTrace_trCapB` (proved, at `cC`), `trCapB_hookGate_init`/`_ccBoot` (proved), traced `traceConfChangeEvent.spec` ★ (`RaftReadLend`), `raft.becomeFollower.traced` (proved) | positions 0-2 by `BootNext` from each previous `Λ` and `Φvs` |
| `RawNode.Bootstrap` traced ★ | `raft.becomeFollower.traced`, `bootMarshal`, traced `raft.applyConfChange` ★ (follower, `_ccBoot`) | positions 3 to `|C| + 3` |
| `trCapB_bootDone` ★ (A8.2) | `simInv`'s `Bt`/`LastOf`/`BootSegs`, `bootEvAt_unique` (existing) | §5.3 |
| `Cluster.traceSim_bootEnd` ★ (A8.4) | `traceDir_agree`, `simInv`'s new clause, `newTrace_bootInit`, `bootInit_eq` | §5.3 |
| `isReadyChan_recvAu.tracedSpec` ★ (revised) | `isReadyChan`'s protocol with `readyP` carrying the escrow element | the element is minted at `run`'s `readyc` commit (§3.2, 3.) |
| `isReadyChan_recvAu` (untraced law) | re-opened: `readyP`'s gated element is dropped | holds for every `γ` |
| `node.Advance.tracedSpec` ★ | `advInv` with `np` lent (§3.2, 4.), `rtkInv` | `pend = false` at the rendezvous in both orders; the claim's key deposited; stale keys too |
| `node.Advance.spec` | re-opened (`advInv`'s gated `np`); text unchanged, every `γ` | `run` needs only `np` back, which the protocol returns whatever the driver holds |
| `node.Step.tracedSpec` (corollary) | `stepIn_intro` (with `trTok`), `node.Step.spec` | — |
| `node.Step.spec` | proof unchanged (`stepWithWaitOption` passes `stepP`) | every `γ` |
| `stepIn_intro` (gains `trTok`) | re-opened: `ApiImpl.stepIn_intro_impl` splits on the trace | §3.2 items 5-6 |
| `trTok_type`, `trTok_untraced` | `trTok`'s body (`TrSent`) | — |
| the five refused `node.X.spec`s (§3.5) | their proofs plus the premise discharging `netP`'s/`stepP`'s untraced arm (`ProposeConfChange`: its internal `stepIn`) | untraced `netP`/`fwdP` unchanged |
| `node.run.gated_of` ★ (one spec at the end) | §3.2's arms: `raft.Step.traced` with `stepBundle_traced` (re-opened), `wp_rn_raft_Step_prop_traced` (re-opened), `RawNode.Tick.traced` (re-opened), `acceptReady.spec` (re-opened), `readyWithoutAccept.spec` (re-opened), traced `RawNode.Advance` ★, traced `raft.applyConfChange` ★† (leader case), `getStatus`, `rtkInv` | the invariants of §3.2 (1.-6.) give each arm's premises (§4); the bounds by the budget |
| traced `RawNode.Advance` ★ | `raft.Step.traced` (self responses: `TrNetTy`, `selfTok`), `stepBundle_traced` on `AckTy` (`.onA`, `stepBundle_traced_storAck`), `TrNoSnap` | 28n's design; `stepsOnAdvance` holds exactly the self responses and the two acknowledgements (`rawnode.go:411-426`) |
| traced `raft.applyConfChange` / `switchToConfig` ★† | `Changer` specs giving back the old maps, `traceConfChangeEvent.spec` over `RaftReadLend` ★, `trCapB_hookGate_applyCC` (proved, booted) / `_ccBoot` (unbooted) | follower case argued (29n); the leader excluded (§3.4, L2) |
| `rnTrace`'s new clauses 1(a)-(c) ★† | established at `setupNode`; kept by the re-opened triples of §3.3 | §3.6 (L1), §3.4 (L2) |
| `raft.Step.traced`, `stepBundle_traced` | proved (30c); re-opened for 1(a)-(c) | gains `OutTyStep` if §3.6's first option is taken (†) |
| `trCapB_hookGate_applyCC`, `traceConfChangeEvent.tracedSpec_proof`, `startTrace_trCapB`, `cluster_alloc_traced`, `harness_alloc`, `Cluster.traceSim_alloc`/`_end`, `tracecheck_Events_traceAccepts`, the checker's Link, `confPolicy_alloc`/`_decide`, `snapshotCert_made`, `snapMade_elem` | proved | — |
| `runOver_intro`, `runOk_at_end` (`HarnessEnd`) | restated over `startDone` (S3); proofs: `Cluster.traceSim_bootEnd` in place of `HD` | — |
| the fire laws, `trCapB_perm`, `Cluster.traceSimInv_alloc` | re-opened for `simInv`'s `Dn` (A8.2) | statements unchanged |

---

## 8. The end-to-end probe (after review)

**The path, in the Go's order**: `StartNode`, `Ready`, `handleReady`, `Advance`, then `send`→`Step`.

The first `Ready` of a fresh voter hands out no message, so the concrete run that reaches a message:
`StartNode` ×3; voter 1's first `Ready` (the three bootstrap entries; `ApplyConfChange` ×3 through
`confPolicy_decide`; `Advance` without using the claim's tokens: `ms = []`); ticks until
`tickElection` campaigns (`hup`: `applied = 3 ≥ |boot|`, §3.4); voter 1's second `Ready` with `MsgVote`
to 2 and 3 (key 1 of voter 1's escrow); `Advance`, giving `trTok` for each `MsgVote`;
`proto.Clone`; `send` → `node.Step` at voter 2; voter 2's `recvc` arm steps the `MsgVote` (`TrNetTy`)
and logs the receive line after voter 1's `Ready` line.

**Probe A (client glue, harness level; easy).** A Lean `example` over the client statements as
hypotheses:
- `harness_alloc`, `tcOpsInv`/`confPolicy_alloc`/`tcSnapsInv`, then `startTraceC_intro`;
- `StartNode.tracedSpec` (A8.3) for one voter;
- `isReadyChan_recvAu.tracedSpec` (revised), giving `readyGotT` with the claim on `ms`;
- `handleReady`'s refutation of a snapshot `Ready` (`snapshotCert_made`, `snapMade_elem`);
- `node.Advance.tracedSpec`, giving `[∗list] q ∈ ms, trTok γ q.st`;
- for `q ∈ ms`: `proto.ClonePb.spec` at `pbMessage`, `trTok_type`, then `stepIn_intro` (with `trTok`)
  and `node.Step.spec` at `q.msg.To'`;
- at the end, `Cluster.traceSim_bootEnd` with the three `startDone`s and `traceDir`, then `runOver_intro`.

It checks that each post supplies the next pre: the claim's `ms` against `readyGot`'s `ms` and
`rd.Messages`; `ClonePb`'s `T.ro` from the `Ready`'s `msgOwn … (readyDq q.st)` and its `T.dec`/`eqv`
into `msgPtsC … ⟨…, []⟩` (S1's correction; the one new glue); `trTok` against `stepIn_intro`'s `st`;
`startDone` into the end law.

**Probe B (node level; hard, chosen by its invariant).** The new invariant is the escrow `rtkInv` with
`run`'s lent `np` (§3.2, 2.-4.), plus `stepP`'s gated token and type (§3.6). Prove, for one node:
1. `run`'s `readyc` arm: the key allocated (`pend := true`, `np` in) and the element into `readyP`; then
   `acceptReady.spec` (its `"Htoks"`) and the deposit (`np` out, `pend := false`).
2. The busy loop state with `np`.
3. The `advancec` rendezvous in both orders (`RcvPending`: the driver's commit with `np` in `advDep`;
   `SndPending`: `run`'s commit reading the driver's key from `req`), yielding
   `node.Advance.tracedSpec`'s tokens; and the same rendezvous with a driver **without** a claim
   (`node.Advance.spec`), which must leave `run` with `np` and nothing else owed; and with a **stale**
   claim.
4. At the receiver, `stepIn_intro`'s traced split into `netP`/`fwdP`, then the `recvc` arm through the
   guard to `raft.Step.traced` with `StepNodeOk` and the token.

The riskiest piece: it checks that untraced `Advance` is provable at a traced node (F3), that the
deposit is found in both orders, and that `TrOutTy` gives `TrSent` at `acceptReady` (G1's sender half).

---

## 9. Links not argued, the order of work, and decisions

**Links I could not argue in full** (all raft-internal; none touches §1):
- **L1 (G1, G2; §3.6). The outbox's types at a traced node, through `raft.Step.traced`.** Re-checked
  in revision 1 against `rawnode.go` (what is handed out: `r.msgs` and non-self `msgsAfterAppend`) and
  per role (§3.6's list). The type list holds of the Go. Not checked: that each path's postcondition
  in slice 30c's assembly pins its queued types (the derivation option), else the `OutTyStep` conjunct
  (one per path).
- **L2 (§3.4). The leader exclusion at the `confc` arm.** Three lemmas now: (i) the bootstrap log
  prefix (argued from `Bootstrap`, `isCommittedLogLb γ boot` and `ownRawNode`'s log agreement); (ii)
  the `confc`-arm lemma (`k + 1 > applied` from A1: the step "undecided at the last `Advance`, so
  `k ≥ applied`" to be read against `undecFree`/`cam`); (iii) **G3, new**: no conf entry past
  `|γ.reBoot|` at a traced cluster (needs an origin invariant on log entries; whether `entTk` gives it
  is not checked). Fallback: 29n's leader line lemma.
- **L3 (§3.5, F2, F3). The client call sites, counted** (by the Go call or the lemma applying the
  spec; `RaftWitness` excluded, it has its own raft; links that only pass `wp_node_X` through not
  counted):
  - `stepIn_intro` (`trTok`, F2): 4 sites (server `InvNet.lean`; kv `deliver.lean`; kvreconf and
    kvdurable `Cluster__step.lean`), each discharged by `trTok_untraced` with a fact it holds, kv's after
    `kvPeerOk` gains it (§3.1).
  - `ReadIndex`: 4 (server `NodeBridge.lean:684`; kv `KV__Read`; kvreconf, kvdurable `Replica__read`).
  - `TransferLeadership`: 3 (kv `KV__TransferLeadership`; kvreconf, kvdurable `Cluster__Disrupt`).
  - `ForgetLeader`: 2 (kvreconf, kvdurable `Cluster__Disrupt`).
  - `ReportSnapshot`: 6 (server `NodeBridge.lean:735`, `NetBridge.lean:69`; kvreconf, kvdurable
    `Cluster__step`, `Cluster__dropped`).
  - `ProposeConfChange`: 2 (kvreconf, kvdurable `Cluster__Reconfigure`); plus raft's own
    `node__ProposeConfChange.lean` (its internal `stepIn`).
  - `Advance`: **0** with F3's choice. Fallback (premise on `node.Advance.spec`): 5 (server
    `NodeBridge.lean:547,618`; kv `KV__run`; kvreconf, kvdurable `Replica__run`).
  - Where the fact comes from: the server's `srvClusterOk` (`srvRaftLogInv`'s, read as
    `isRaftNodeIfc_of_isNode` does at `NodeBridge.lean:510`); kvreconf's and kvdurable's `isClusterC`
    `%Htr0` (their replica lemmas, `Replica__read`/`Replica__run`, take it from the cluster predicate if
    they hold it, else their replica predicate gains it: to check at threading); kv holds it only at
    allocation, so kv's `kvPeerOk` and its replica predicate (`isReplica`, for `KV__Read`,
    `KV__TransferLeadership`) gain it. In all, about 21 call sites in 16 files: the server 3 files, kv 3
    (+ `Cluster.lean`'s and the replica's definitions), kvreconf 5, kvdurable 5.
- **L5 (new). `TrNoSnap`'s source at `setupNode`.** `rnTrace` holds `TrNoSnap s.gh.tr s.logst` ("a
  traced caller has it from the Draft's P2"). Its source is Q6 item 8's gated storage bound
  (`storBnd`'s conjunct `⌜c = 0 ∨ γ.raft.reTrace = none⌝`, `InvNodeRule.lean:644`, not yet gated in
  Lean): no compaction right at a traced cluster. Revision 0 did not name it. Its cost is the storage
  contract's clients (the harness never compacts: `SnapshotEvery = 0`; untraced clients by their fact).
- L4 (revision 0's `threadBound ≤ 2^31`): closed by F1 (§6).

**The order of work (S5, S9): no `sorry` under an existing result.**
1. Each sealed definition changes as a gate whose `none` arm is today's body (`stepP` through
   `netP`/`fwdP`, `readyP`, `advInv`/`advDep`/`advRet`, `AdvReq`, `rnTrace`'s clauses, `readyTok`,
   `trTok`, `storBnd`). Every proof of today's untraced results has `γ.raft.reTrace = none` (the
   premise of `node.run.spec`, `StartNode.spec`, `RestartNode.spec`, or the client's fact) and is
   re-proved by rewriting the gate: no `sorry`, every closed theorem unchanged (the acceptance test).
   `node.Advance.spec`'s and `isReadyChan_recvAu`'s re-proofs, which hold for every `γ`, come with the
   escrow (they need `np`'s return and the element's drop, both of which they have).
2. `stepIn_intro`'s premise and the five refusals land with their call sites (L3), each discharged.
3. The traced arms are proved as theorems with the ★ callees as **hypotheses**:
   `node.run.gated_of (hAdv : RawNode.Advance.tracedSpec) (hCC : raft.applyConfChange.tracedSpec) : node.run.gatedSpec`
   (no premise on the trace). Nothing existing depends on it.
4. Only when `hAdv` and `hCC` are proved is `node.run.spec` replaced: it becomes the gated statement
   (premise dropped), and today's statement survives as its instance (`node.run.spec_untraced`, if a
   caller still names it). `StartNode.gatedSpec` and the traced `Advance`/`Ready` are proved after.
   Deriving `node.Advance.spec` from a traced spec, which revision 0 proposed, is gone (F3).

**Decisions taken in this pass (the agent's, recorded in `notes/decisions.md`, "Design pass (node
API, harness)" and "Design pass, revision 1"):**
- the tokens at `node.Advance` through a claim on a per-node escrow (`rtkInv`, `np`), `run` needing
  nothing back, so `node.Advance.spec` unchanged (F3);
- one proved `node.Step.spec`, the gate in `stepIn`'s body, `stepIn_intro` taking `trTok` (F2);
- `TrSent` in the sealed `trTok`, and `trTok_type`;
- the five refused calls (`ProposeConfChange`'s premise used by its proof);
- the leader case of `confc` excluded rather than proved (three lemmas, L2);
- A8's exact form, with S2-S4's and S11's corrections;
- Q33 by the existing `strconv.Itoa` axiom; the harness's `proto.Clone` by the existing `ClonePb` at
  `pbMessage`;
- Q34's local `netJoin` (under the instance) and `join3`; Q35 (a);
- the harness's invariants `tcOpsInv`, `confPolicy`, `tcSnapsInv`;
- the order of work above.

**The user's:** §1 only, settled: Q32 (the premise bundle) and **Q38 (decided by the user, 2026-11-11):
`n + 2 ≤ 2^31` and `[ThreadBoundLe GF (2^31)]`, and the corollary's form**. No other change to a closed
statement or to the trust base is proposed. The tracecheck collection's baseline will gain the
existing axioms of §6 when `RunConcurrent` is proved (a collection update, not a trust-base change).
