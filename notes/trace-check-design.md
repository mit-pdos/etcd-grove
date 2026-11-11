# Trace-check: the design pass, from the closed theorem down to the proved pieces (2026-11-11, revision 2)

The user approved this pass (2026-11-11) under `notes/spec-first-plan.md`'s *Design before plumbing*:
before more threading, the whole chain is written as text, each statement with what it is proved
from and why that suffices, for review. Nothing here is threaded or proved. Every Lean
statement below is a text sketch, **not typechecked** (no Lean was run). Old → new is given wherever
a statement exists today. Revision 0: branch `trace-check-design`, from `trace-check` at `c2325abf53`.
Revision 1: branch `trace-check-design2`, from `trace-check` at `886be91e1b`, after the review round
`notes/trace-validation-reviews/design-r1.md` (first tier F1-F3, second tier S1-S12).
Revision 2: branch `trace-check-design3`, from `trace-check` at `2a0b56856b`, after the review round
`notes/trace-validation-reviews/design-r2.md` (first tier A1-A6, second tier B1-B7).

Reading order: §1 is the only part the user reviews (settled: Q32 and Q38 decided by the user). §2-§6
are the agent's (intermediate statements, recorded per "The gates, delegated"). §7 is the whole chain
as one table. §8 is the probe to run after review. §9 lists the links that are not argued, the order
of work that keeps every existing result proved, and the decisions.

Vocabulary used throughout: `TrNetTy t` (`MsgApp`, `MsgAppResp`, `MsgVote`, `MsgVoteResp`,
`MsgHeartbeat`, `MsgHeartbeatResp`), `AckTy` (`MsgStorageAppendResp`, `MsgStorageApplyResp`),
`recvTokOf` (`TracedRecvTok.lean`), `trTok` (today `TracedNodeApi.lean`; revision 1 moves it to
`InvNode.lean`, §3.1), the capability `trCapB` (`TracedCap.lean`), `rnTrace` (`InvRawnode.lean`).

---

## Revision 2 (2026-11-11): what each finding of `design-r2.md` changed

The six first-tier items are raft-internal; their direction was decided by the coordinator (an
intermediate statement each), their form here by the agent. §1 is unchanged.

**First tier.**
- **A1 (the escrow, the driver sending first).** The review is right: in `SndPending` `run` holds no
  fragment of the driver's key, so it cannot give "key `j` deposited". Of the two fixes, **(b) a
  persistent allocation bound** is taken (simpler: every payload that crosses `advancec` stays
  persistent, and `run` never touches the driver's exclusive element or the tokens). `NodeNames` gains
  `al`; `rtkInv` gains `monoNatAuth γn.al a` (the keys allocated); the claim carries
  `monoNatLb γn.al (j + 1)`, minted with the key at the `readyc` commit; the driver's `SndPending`
  payload carries that lower bound; `run`, meeting it with `np` in hand, reads `j + 1 ≤ a` and answers
  `monoNatLb γn.dep (j + 1)`. Both hand-off orders are argued against `node.go`'s `run` (§3.2 item 4);
  the rendezvous is added to Probe B item 3 with the payload (§8). Rejected: (a), the element in the
  payload (an exclusive resource across the rendezvous, and `run` then hands out tokens).
- **A2 (L1, the outbox's types).** The derivation option is struck. The smallest addition is in
  **`stepBundle_traced.statement`'s post**, not in `stepClose`'s definition: the caller's end resource
  `Gout s'` (today `∃ bt', trCapB …`) gains `⌜OutTyStep s s'⌝`, a pure fact each path proves at its close
  from the messages it queued; `raft.Step`'s code proof is untouched (it returns `Gout s'` as it is),
  and `raft.Step.tracedTriple`'s post carries it to `rnTrace`. The path files re-opened are listed in
  §3.6 (the 30c assembly's paths: planned work). §3.6's exclusion of `MsgSnap` now cites `TrNoSnap` at
  `maybeSendAppend` and `raft.send`'s traced premise, not `ReplSends`. **Found while designing it:** the
  abstract outbox cannot see every handed-out message: a message whose type has no abstraction
  (`msgAbs … none`, dropped by `absList`) is invisible to any outbox conjunct, and `XfOk`'s
  `SentMsgShape` admits two such types raft queues, `MsgTimeoutNow` and a forwarded
  `MsgTransferLeader`. So `OutTyStep` has a physical half: `raft.send.spec`'s traced premise excludes
  untyped messages, `XfOk` records it of the queues, and `raft.Step.spec` gains the two traced premises
  its `sendTimeoutNow` and forwarding branches need (§3.6, "The physical half").
- **A3 (G3).** Restated as a joint invariant, with `appliedTo`'s automatic leave among the sources:
  (a) no entry past the bootstrap log is a configuration entry, cluster-wide, owned by the term logs'
  authority (where every entry of every log is minted), gated on the trace; (b) no node's configuration
  is joint, per node, a new clause 1(d) of `rnTrace`. (a) is kept because a traced leader mints only
  normal entries (`raft.Step.spec`'s existing traced premise on `MsgProp`, `becomeLeader`'s empty normal
  entry), the automatic leave being excluded by (b) through `raft.Step.spec`'s existing `autoLeave`
  premise; (b) is kept because the `confc` arm applies only a committed entry, a bootstrap `AddNode` by
  (a). The registry route is dropped (it cannot see an empty `ConfChangeV2`, a filler). §3.4 item 4.
  29n's leader line lemma stays the fallback.
- **A4 (L5, `TrNoSnap`).** Taken: **(a), the update form**,
  `TrNoSnap tr ls := □ (⌜tr ≠ none⌝ -∗ (⌜prev.index ≠ 0⌝ ∨ storPast ls.storage 1) -∗ |={⊤}=> False)`.
  Its two uses (`raft__maybeSendAppend.lean`'s snapshot fallbacks) are WP steps of a plain triple at
  `⊤`, so `iapply` becomes `imod`; the other mentions pass `TrNoSnap` through by name. `setupNode` builds
  it from the client's `isStorage γ K st` (its `Hbound` at the gated `storBnd`), before the conversion to
  raft's `raftBnd`, which therefore needs no gate. Rejected: (b), a pure "never compacted" fact in the
  storage key's names (a change to MemoryStorage's ghost state for one premise). L5 is closed (§5.2).
- **A5 (one proved triple for `node.Advance`).** `node.Advance.tracedSpec` is the one proof;
  `node.Advance.spec` (text unchanged) is its instance at `ms = []`, by the law
  `readyToksClaim_nil : ⊢ readyToksClaim n γ N []`, the claim being `⌜ms = []⌝ ∨ (the escrow element)`
  at a traced cluster and `True` at another. The left disjunct is the claim-less driver of F3: its
  request records `none`. No client changes (§3.1).
- **A6 (`handleReady`'s `ConfChangeV2` arm).** Handled as kvreconf's `Replica__applyEntry`, from facts the
  client sees: the committed entry decodes (`tc_confShaped`, from a new pure clause of `tcOpsInv` and
  kvreconf's `confShaped_of_ops` argument: past the bootstrap log the harness's committed requested
  entries are normal, and an empty `ConfChangeV2` decodes by the existing `ccDecodeV2_nil`), so
  `proto.Unmarshal` returns no error and the `panic` is not reached; `confPolicy_decide` then
  `node.ApplyConfChange.spec`, the membership step given by raft's exported `committed_emptyV2_joint`
  (an empty `ConfChangeV2` is committed only where the configuration in force is joint). Not dead in the
  proof, though it is in every run (G3).

**Second tier.**
- **B1 (the order of work).** Steps 1 and 2 are **one landing** (the gates with their client-side
  premises and every call site). `rnTrace`'s new clauses stay off proved theorems until their facts are
  proved: a landing of their facts first (L1's per-path `OutTyStep` and its physical half, lemmas (i),
  (ii), G3 (a), `TrNoSnap`'s form), then a landing adding the clauses with every re-opened triple
  re-proved in it. A8.1's `simInit` readers are re-proved in A8's own landing (done on branch
  `trace-check-a8`: every reader re-proved, no `sorry`; §5.3). `node.run.gated_of`'s hypotheses are
  then only `hAdv` and `hCC`, every other link being a theorem before it is stated (§9).
- **B2 (L3 and `storBnd`'s clients).** Three client lemmas unfold `storBnd` (`kvJ_bnd`, `kvrJ_bnd`,
  `kdJ_bnd`) and the server reaches it through raft's `memStorage_isStorage` (`NodeStart.lean:322`).
  Raft exports `storBnd_intro_untraced` and `storBnd_zero`; the three lemmas are re-proved through them
  (no unfold, as PRINCIPLES asks), `memStorage_isStorage` gains the untraced premise (Q6 item 8). L3
  gains 4 call sites in 4 files (§9).
- **B3 (lemma (ii)).** Written in the short form: `uint.nat s.logst.applied ≤ rs.capplied`, a new
  clause 1(e) of `rnTrace` (traced only), established at `RawNode.Advance` (`advRS` sets `capplied := ca`); at the `confc` arm
  `DynCCPre` gives `rs.capplied ≤ k` (§3.4 item 3).
- **B4 (`pbMessage`'s import).** `PbMessage.lean` moves from rafthttp's proof tree to raft's, beside
  `InvPbMsg` (its body uses only `InvProto` and `InvPbMsg`; the `Net` import goes), listed in
  `etc/api/raft.txt`; rafthttp's importers import the new module. The harness then depends on raft and
  protobuf only (§2.3).
- **B5 (`app`'s thread token).** `RunConcurrent` forks each `app` with `wp_fork_tok_body`
  (`Lifting.lean`), handing it the fresh token; `app` keeps one token in its loop invariant, deposits it
  at each `c.net.Add(1)` and gets a fresh one at each `go` (`wp_fork_tok_self`), and returns it at exit
  (§2.2, §6; checked in Probe A).
- **B6 (masks; the escrow's namespaces).** `rtkN := N.@"rtk"`, a sibling of the `readyc` and
  `advancec` channels' namespaces; `rtkInv` is opened inside a channel AU at `⊤ ∖ ↑(that channel's
  namespace)`, by whichever thread executes the commit (§3.2 item 2).
- **B7 (`acceptReady`).** `acceptReady` frames 1(c) and 1(d) (it moves `applying`, not `applied`, and
  keeps the role and the configuration), establishes 1(a) by the `Ready` line, and empties the outbox
  (1(b) trivially); its re-opening is for `readyTok`'s body and those (§3.3).
- `ThreadBoundLe.weaken`'s instance argument is instance-implicit: §2.1 now writes
  `haveI := ThreadBoundLe.of_eq HT; ThreadBoundLe.weaken (n + 2) Hn`.

**Re-checked.** §7's provenance column, row by row against the changes above; §8's probes (Probe B
item 3 with the allocation bound; Probe A with `app`'s token, the `ConfChangeV2` arm, the moved
`pbMessage`). Aligned with amendment A8 as implemented (branch `trace-check-a8`, §5.3): a mono list
for the witnesses, not a ghost map; `bootInit` deleted, `newTrace_simInit`; `HarnessEnd`'s `bootEnd`
a theorem.

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
  makes `haveI := ThreadBoundLe.of_eq HT; haveI : ThreadBoundLe tcGF (2 ^ 31) :=
  ThreadBoundLe.weaken (n + 2) Hn` (`weaken`'s instance argument is instance-implicit, so it is not
  passed positionally; revision 2), or `⟨by rw [HT]; omega⟩`, as `cache/Results.lean`, `Hbound : receiptBound tcGF + 3 ≤ 2^61` by
  `rw [HN]; omega` from `n + 4 ≤ 2^31 + 2 ≤ 2^61`, and `ihave #Hprem' := Hprem hG` as
  `etcd_putget_adequate` does.
- **`TcOpen`** is deleted once `RunConcurrent.wp_proof` exists. `Results.lean` then states §1.

### 2.2 `RunConcurrent`'s body (`concurrent.go`), call by call

The harness's own invariants (named here, S12), allocated after `harness_alloc`, all outside `N`
(raft's namespace):
- **`tcOpsInv γ := inv tcOpsN (∃ ops, ownCommittedOps γ ops)`**, from `harness_alloc`'s
  `ownCommittedOps γ boot`. `γ.dup = false`, so `node.Propose.spec` takes one non-persistent AU per
  call, `AU <{ ∃∃ ops, ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅ <{ ∀∀ t, ownCommittedOps γ (ops ++ [⟨t, 0, data⟩]), COMM True }>`;
  the proposer builds it from `tcOpsInv` (open, take, close with the appended list). **Revision 2
  (A6):** the invariant also holds the pure clause `boot <+: ops ∧ ∀ op ∈ ops.drop boot.length,
  op.type = W32 0` (the requested entries past the bootstrap log are the proposer's normal ones), from
  which `∀ op ∈ ops, op.isConfChange → ConfShaped op` follows (kvreconf's `%Hsh`: `boot`'s three
  `AddNode`s decode by `BootLogFacts`; a type-`0` entry is no conf entry, kvreconf's
  `confShaped_normal`); kept by each proposal (type `0`). `boot` has no filler, so a committed entry at
  a position `k ≥ |boot|` that is a requested entry is one of `ops.drop boot.length`. `handleReady` reads it through
  `tc_confShaped : tcOpsInv γ -∗ isCommittedLogLb γ l ={E}=∗ ⌜∀ e ∈ l, e.isConfChange → ConfShaped e⌝`,
  proved as kvreconf's `rkv_confShaped` (`ownCommittedOps_lb_prefix` and the pure `confShaped_of_ops`,
  which moves from kvreconf's `Rule.lean` to raft's client library `ConfRule.lean`, beside `ccDecode`, so
  both use one copy). Nothing else of the run reads the committed operations.
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
| (ghost) | `harness_alloc` (`HarnessAlloc.lean`): `traceNames_alloc`, `cluster_alloc_traced`, `Cluster.traceSim_alloc`; then `tcOpsInv`, `confPolicy_alloc`, `tcSnapsInv` | `traceNames_alloc` also allocates `monoListAuthOwn tn.dn 1 []` (A8.2, as implemented: §5.3) | the traced cluster `γ`, `traceDir γd tn`, `Cluster.traceSim γ vs tn`, each voter's `voterStart` |
| `raft.NewMemoryStorage()`, `&raft.Config{…}` | the storage contract (`restartStorage`, as kvreconf), its justification `J` never compacting (`J.B k := ⌜k = 0⌝`), its bound by the new law `storBnd_zero` | the storage bound `storBnd` gated (Q6 item 8): no compaction right at a traced cluster; `storBnd_zero`, `storBnd_intro_untraced` exported (B2) | `ConfigValid`, `TraceLogger ≠ nil` (`c.rec`), `MaxSizePerMsg = ^0`, `AsyncStorageWrites = false` |
| `raft.StartNode(rc, peers)` ×3 | `StartNode.tracedSpec` (`TracedNodeApi.lean`) | **`D` fixed** (A8.3): the post's `startDone γ D cv.ID'` becomes the sealed `startDone γ cv.ID'` | `isNode`, `nodeDriver … init`, `nodeConfig`, `nodeRunning 1`, the persistent `startDone` |
| `c.apps.Add(1); go c.app(r)` ×3 | `sync.join` (`WaitGroupJoin`: three `Add(1)`s, `num_added ≤ 3`); the `go` by `wp_fork_tok_body` (`Lifting.lean`) | the thread token named (B5) | each `app` gets `nodeRunning 1`, `isNode`, the driver state, a third of the network's adder right (§6, Q34), `ownDone apps P'` with `P' := nodeRunning 1 ∗ njAdder ⅓`, and **the fork's fresh `threadTok`**, which its body must return (it ends holding one: §2.4, §6). The other goroutines (drivers, proposer, isolation) take none: `wp_fork` |
| `drivers.Add(3)` | a local `join3` lemma over the raw `WaitGroup.Add` spec (three `ownDone`s from one `Add(3)`; `join` has `Add(1)` only) | new (harness-local, glue) | three driver goroutines |
| isolation driver | `time.Sleep`, `atomic.Uint64.Store`, `below` (proved) | unchanged | nothing of raft |
| proposer | `below`, `context.WithTimeout`, **`strconv.Itoa`** (existing axiom, §6 Q33), `node.Propose.spec` (unchanged) with the AU from `tcOpsInv`, `cancel`, `atomic.Int64.Add`, `time.Sleep` | unchanged | `Propose` puts one **normal** entry on `propc` (`propP`'s first disjunct), which the traced `propc` arm needs (`PropAny`) |
| conf-change proposer | `time.Now` (Perennial's trusted spec) and `time.Time.Add` (proved), once before the loop (`concurrent.go:206`); then `atomic.Int64.Load` of `ConfChanges` at a persistent `0` (`Workload`'s `ConfChanges' = 0`: the loop's `&&` short-circuits, so the loop's `time.Now().Before`, `Status` and `ProposeConfChange` are never called) | **corrected** (S1: revision 0 said `time.Now` is never called) | the counter is never written; its points-to is made persistent at allocation |
| `drivers.Wait`, `time.Sleep`, `close(c.stop)` | `join3`, `time.Sleep`, the channel close | unchanged | — |
| `c.apps.Wait()` | `sync.join.WaitGroup.wp_Wait` | unchanged | the three `nodeRunning 1` and the three `njAdder ⅓` back |
| `r.node.Stop()` ×3 | `node.Stop.spec` | unchanged | `nodeRunning 1` in |
| `c.net.Wait()` | `netJoin` (§6, Q34): `njClose` (`njAdder 1` → the wait token), then the raw `Wait` | new (harness-local) | the counter reaches 0 (every network goroutine `Done`) |
| `return c, nil` | `runOver_intro` (`HarnessEnd.lean`) over `startDone`, with the API law `Cluster.traceSim_bootEnd` (A8.4) | the hypothesis `BootEnd D` becomes the theorem `bootEnd` (done on `trace-check-a8`); `runOver_intro` takes `□ [∗list] i ∈ vs, startDone γ i`, `traceDir γd tn`, `Cluster.trace γ = some γd` (S3) | the three `startDone`s, `nodeBoot`, `Cluster.traceSim` |

### 2.3 `app` (one per replica)

| Go | Statement used | Old → new |
|---|---|---|
| `time.NewTicker(c.cfg.Tick)`, `defer ticker.Stop()` | Perennial's `time.NewTicker.spec` (proved; needs `0 < Tick`: Q35) | unchanged |
| `case <-c.stop: return` | the closed-channel receive; `apps.Done` with `nodeRunning 1 ∗ njAdder ⅓` | unchanged |
| `case <-ticker.C: r.node.Tick()` | `node.Tick.spec` (`isNode` only) | unchanged: its traced content is `run`'s `tickc` arm |
| `case rd := <-r.node.Ready()` | `isReadyChan_recvAu.tracedSpec` | **changed** (29n finding 4): `readyGotT`'s last conjunct is the claim `readyToksClaim n γ N ms`, no longer the tokens (§3.1); revision 2: the claim also carries the key's allocation bound (A1) |
| `c.handleReady(r, rd)` | `raft.IsEmptySnap`, `MemoryStorage.Append`/`SetHardState` (storage contract), `proto.Unmarshal` into a `*ConfChange` (`proto.UnmarshalConfChange.spec`, existing axiom), **`node.ApplyConfChange.spec`** with `confDecided` from `confPolicy_decide` (§2.2), `atomic.Int64.Add` | the snapshot branch refuted from client-visible facts (S12): `readyGot`'s `readyRest` holds `readySnap … L`; at `L = some l` it holds `snapshotCert γ N …`, whence `snapshotCert_made` gives `snapMade γ s` and `snapMade_elem` against `tcSnapsInv`'s `ownSnapsMade γ []` gives `s ∈ []`; at `L = none`, `rd.Snapshot' = null`, so `IsEmptySnap` is true. **Both conf arms** (revision 2, A6: as kvreconf's `Replica__applyEntry`): the entry `e` at position `k` is committed (`readyGot`'s `committedEntriesAt` with `isCommittedLogLb`), so `tc_confShaped` (§2.2) gives `ConfShaped e`: it decodes, `proto.Unmarshal` returns no error (`proto.UnmarshalConfChange.spec` / **`proto.UnmarshalConfChangeV2.spec`**, existing axioms) and the `panic` (`concurrent.go:315-317`, `:322-324`) is not reached. Then `confPolicy_decide` (rule `ccDecode`, decision `.apply o`) and `node.ApplyConfChange.spec` at `confAt γ k m` (the driver's view), whose premise `Membership.applyChange o m = some m'` holds: for a `ConfChange` past the bootstrap log, impossible (it would be among the requested entries, which are normal past `boot`), at a bootstrap position the voter's `AddNode` into `m ∋` it; for a `ConfChangeV2`, `e` is not a requested entry (same reason), so `e.isEmptyV2` (`opsOf`), and raft's exported **`committed_emptyV2_joint`** (`InvNodeRule.lean:365`) gives `m.isJoint`, where the empty change (the leave) applies. The arm is reached in no run (G3), but its proof needs no raft-internal fact. The `CreateSnapshot`/`Compact` branch: `SnapshotEvery = 0` |
| `r.node.Advance()` | **`node.Advance.tracedSpec`** (new, §3.1; the one proof, `node.Advance.spec` its instance, A5) | the claim in, `[∗list] q ∈ ms, trTok γ q.st` out. The stopped disjunct is refuted by `nodeRunning_stopped`: the `app` holds `nodeRunning 1` |
| `for _, m := range rd.Messages { c.send(r, proto.Clone(m).(*pb.Message), …) }` | **`proto.ClonePb.spec`** (existing axiom) at `pbMessage` (the `PbType` of a `*raftpb.Message`; revision 2, B4: `PbMessage.lean` moves from `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/` to `Proof/go_etcd_io/raft/v3/`, beside `InvPbMsg`, dropping its import of rafthttp's `Net`, which its body does not use, and is listed in `etc/api/raft.txt`; rafthttp's importers import the new path; the harness then imports no server module), `below`, `send` (below) | **corrected** (S1): revision 0 said "`proto.Clone` as kvreconf"; kvreconf copies messages by hand (`copyMsg`), and the generic `proto.Clone.spec` has no `Message` case. Glue to check in Probe A: `ClonePb`'s `T.ro l m` from the `Ready`'s `msgOwn q.loc (readyDq q.st) q.st`, and the clone's `T.dec l' m'` with `eqv` into `node.Step`'s `msgPtsC … ⟨st.msg, st.ents, st.snap, st.ctx, []⟩` (the etcd server's `netRecv` does the same from a decoded copy) |

**When the harness sends, checked against the Go.** `app` calls `handleReady`, then `Advance`, then
`send` for each message (`concurrent.go`, the comment at the loop). `node.Advance` returns only once
`run` has taken the `advancec` rendezvous (or is stopped). `run` arms `advancec` only in the `readyc`
arm, after `n.rn.acceptReady(rd)` has returned (`node.go:435-446`), and `acceptReady` ends with
`traceReady`, the `Ready` line that mints the tokens. So every message is handed to the network after
its sender's `Ready` line, and the tokens are there at `Advance`'s return.

### 2.4 `send` (one goroutine per message)

| Go | Statement used | Old → new |
|---|---|---|
| `c.net.Add(1)` (in `app`), `go func(){…}` | `netJoin.wp_Add` (§6, Q34): the caller's `njAdder ⅓` and its thread token in, `njDone` out; the `go` by `wp_fork_tok_self`, which gives `app` a fresh token back (B5) | new (harness-local) |
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

Design rule (revised, F2/F3; revision 2, A5): **one proved spec per function**; a gate lives in a
sealed predicate (`stepIn`, `nodeDriver`, `isNode`'s invariants), never as a second triple to keep in
step with the first. Where a traced client needs more than today's post (`Ready`, `Advance`), the
traced statement is **the one proof**, and today's spec, text unchanged, is its instance (a corollary,
never a second proof): `isReadyChan_recvAu` drops the claim, `node.Step.tracedSpec` is
`stepIn_intro` with `node.Step.spec`, and `node.Advance.spec` is `node.Advance.tracedSpec` at `ms = []`
(`readyToksClaim_nil`). Every one of them holds for every `γ`, traced or not, so no existing client
changes but §3.5's refusals and F2's `stepIn_intro` premise.

| Function | Old (today) | New |
|---|---|---|
| `StartNode` | `StartNode.gatedSpec` (frozen Draft, over `startTrace`); `StartNode.tracedSpec D` (hypothesis, `D` free) | A8.3: the gated post gains `startDoneB γ cv.ID'`; `StartNode.tracedSpec` has no parameter, its post the sealed `startDone γ cv.ID'`. Proved from `setupNode`'s traced spec (§5) |
| `node.Tick` | `node.Tick.spec` | unchanged |
| `node.Ready` / `isReadyChan_recvAu` | untraced law; `.tracedSpec` (hypothesis) with `readyGotT` = `readyGot` ∗ `[∗list] q ∈ ms, trTok γ q.st` (**unprovable**, 29n finding 4) | `readyGotT` = `readyGot` ∗ **`readyToksClaim n γ N ms`**. `.tracedSpec` a theorem; `isReadyChan_recvAu` stays proved for every `γ` (it drops the claim) |
| `node.Advance` | `node.Advance.spec` (no tokens) | New **`node.Advance.tracedSpec`**, the one proof (A5): `node.Advance.spec`'s pre ∗ `readyToksClaim n γ N ms`; post: its first disjunct ∗ `[∗list] q ∈ ms, trTok γ q.st`; the stopped disjunct gives nothing. **`node.Advance.spec`: text unchanged, every `γ`, now its instance** at `ms = []` (`readyToksClaim_nil` in, the empty list out). F3: `run` needs nothing back |
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
Untraced `True`. Traced: `ms = []` (nothing claimed: F3's claim-less driver, whose request records
`none`; revision 2, A5), or the driver's element of the node's escrow (`rtkInv`, §3.2 item 2) at the
`Ready`'s key `j`, recording `ms`, with the persistent bound "key `j` allocated" (`monoNatLb γn.al
(j + 1)`; revision 2, A1). **A departure from "no identification handles"** (PRINCIPLES): a
resource every traced driver threads from `Ready` to `Advance`. It carries content (which messages
the tokens are for), and a driver that drops it loses only the tokens, never the node's progress.
Alternative considered: keep `ms` inside the sealed `nodeDriver`, which needs a field of the
client-visible `NodeDriverState` (and `afterReady`'s argument) set by every client. -/
@[no_expose] def readyToksClaim (n : Loc) (γ : Cluster) (N : Namespace) (ms : List QMsg) : IProp GF :=
  match Cluster.trace γ with
  | none => iprop(True)
  | some _ => iprop(⌜ms = []⌝ ∨ ∃ γn j, ⌜NodeOk γ γn ∧ γn's node is n⌝ ∗ isNodeChan γn … ∗
      ghostMapElem γn.rtk j (DFrac.own 1) ms ∗ monoNatLb γn.al (j + 1))

/-- (A5) Nothing claimed: what `node.Advance.spec` (the instance) passes. -/
theorem readyToksClaim_nil (n : Loc) (γ : Cluster) (N : Namespace) : ⊢ readyToksClaim (GF := GF) n γ N []

/-- (A5) **`node.Advance`'s client spec, the instance**: `node.Advance.tracedSpec` at `ms = []`,
`readyToksClaim_nil` for the claim, `[∗list] q ∈ [], _` dropped. Its text is today's. -/
theorem node.Advance.spec_of_traced (h : node.Advance.tracedSpec) : node.Advance.spec

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
1. **`ownRawNode`'s traced conjunct** (`rnTrace`, slice 25n) gains (added only once their facts are
   proved, §9's order, B1):
   - *(a) flag to delivery* (29n finding 2): `rs.delivered ≠ [] → b = true` for the capability's
     `∃ b`. `rnTrace` takes `rs.delivered` (or the clause sits next to it in `ownRawNode`).
   - *(b) the outbox's types* (§3.6, G1; revision 2, A2): `TrScope s ∧ ∀ m ∈ s.outbox, TrOutMsg m`, with
     `TrScope s := s.lt = W64 0 ∧ ReadIdle s` (no transferee; no pending read: `s.rd.ro`'s queue and
     `s.rd.pend` empty). Kept by `raft.Step.tracedTriple`'s new `OutTyStep` (§3.6). The physical queues'
     half is in `XfOk` (§3.6), not here.
   - *(c) the leader exclusion* (§3.4): `s.role ≠ follower → applied ≥ |γ.reBoot|`.
   - *(d) no joint configuration* (revision 2, A3: G3 (b), §3.4 item 4): `c.outgoing = ∅ ∧
     c.autoLeave = false` for the configuration `c` the struct is at.
   - *(e) applied below the configuration index* (revision 2, B3: lemma (ii), §3.4 item 3):
     `uint.nat s.logst.applied ≤ rs.capplied`. In `rnTrace` (traced only, so that no untraced proof is
     re-opened for it), which takes `rs.capplied` beside `rs.delivered`.
2. **The node's token escrow** (F3; new, per node). `NodeNames` gains the fields `rtk : GName` (a ghost
   map `Nat ↦ List QMsg`, the `Ready`s' keys), `np : GName` (an exclusive token), `dep : GName` (a
   monotone count of the keys deposited) and (revision 2, A1) `al : GName` (a monotone count of the keys
   allocated), allocated in `newNode`/`setupNode` (per node, S12). A new invariant, in `isNodeChan`
   (persistent), gated, in the namespace `rtkN := N.@"rtk"` (revision 2, B6: a sibling of the `readyc`
   and `advancec` channels' namespaces, so that it can be opened inside either channel's AU, at
   `⊤ ∖ ↑(that channel's namespace)`, by whichever thread executes the commit):
   ```
   rtkInv γn := inv rtkN (∃ (M : GMap Nat (List QMsg)) (a : Nat) (pend : Bool),
     ghostMapAuth γn.rtk 1 M ∗ ⌜dom M = [0, a)⌝ ∗ (if pend then own γn.np (Excl ()) else True) ∗
     monoNatAuth γn.al a ∗                                   -- revision 2 (A1)
     monoNatAuth γn.dep (if pend then a - 1 else a) ∗
     [∗map] j ↦ ms ∈ M, ⌜j < (if pend then a - 1 else a)⌝ -∗
        (([∗list] q ∈ ms, trTok γ q.st) ∨ ghostMapElem γn.rtk j (DFrac.own 1) ms))
   ```
   (`pend`: the last key's tokens not yet deposited; a key below the deposited count stays deposited,
   since the count only grows. The slots hold the client's `trTok` bodies, `⌜TrSent q.st⌝ ∗
   recvTokOf …` (revision 2: not `readyTok`, so that the escrow and `node.Advance.tracedSpec` land before
   `readyTok`'s body gains `TrSent`, §9's order); `run`'s deposit turns `acceptReady`'s `readyTok`s,
   whose traced body becomes the same, §3.6, into them.) The claim, traced: §3.1's `readyToksClaim`
   (`⌜ms = []⌝`, or the element `j ↦ ms` with `monoNatLb γn.al (j + 1)`).
   `run`'s loop invariant holds `own γn.np (Excl ())` whenever no deposit is pending (idle and busy).
3. **`readyc` commit** (`readyP`, the `readyc` payload): `run` opens `rtkInv`, inserts the fresh key
   `a ↦ ms` (the `Ready`'s handed-out messages), raises `al` to `a + 1` and takes
   `monoNatLb γn.al (a + 1)`, sets `pend := true` by putting `np` in, and puts the element `a ↦ ms` with
   that bound (the claim's right disjunct) into `readyP`. **After `acceptReady`** (same arm, before
   `advancec` is armed, `node.go:436-438`): `run` opens `rtkInv` with `acceptReady`'s `"Htoks"`, takes
   `np` back, sets `pend := false`: key `a`'s tokens are now deposited (`dep` raised to `a + 1`).
4. **`advInv`** (the `advancec` protocol). `run` lends `np` at the rendezvous: `advDep` (run first,
   `RcvPending`) and the `SndPending → RcvCommit` step (driver first) carry it. The driver's request
   `γ.req` (fixed name; `AdvReq` gains `Option Nat`) records its claim's key `j`, or `none` (untraced, or
   the claim's left disjunct `ms = []`).
   - **`RcvPending` (run first).** `advDep` gains `own γn.np (Excl ())`. The driver, at its send's
     commit (inside the channel's AU), opens `rtkInv`: `pend` is `false` (else the invariant's `np` and
     `advDep`'s are two), so the deposited count is `a`; its element gives `j ∈ dom M = [0, a)`, so
     `j < a` and the key's slot holds the tokens (not the element: the driver holds that one, and two
     full elements conflict). It swaps its element in and takes the tokens. It leaves `np` in `advRet`
     for `run`.
   - **`SndPending` (driver first; revision 2, A1).** The driver's payload in `advInv` is persistent
     only: `req`'s half with `j` and **`monoNatLb γn.al (j + 1)`** (a copy of its claim's bound); its
     element stays with it. This order can start while `pend = true` (the driver got its claim at the
     `readyc` commit and may call `Advance()` before `acceptReady` returns). `run` reaches its `advancec`
     receive only after the deposit, holding `np`; it opens `rtkInv`: `pend = false`, so
     `dep`'s count is `a`, and the payload's bound against `monoNatAuth γn.al a` gives `j + 1 ≤ a`; it
     mints **`monoNatLb γn.dep (j + 1)`** and puts it in the `RcvCommit` answer (with the agreeing `req`
     half). The driver, at `RcvCommit → Idle` or later, opens `rtkInv` with its element and that bound:
     `j` is below the deposited count whatever `run` has allocated since (`pend` may be `true` again, for
     a later key `a' - 1 ≥ j + 1`), so its slot holds the tokens; it swaps its element in and takes them.
   - A driver without a claim (`ms = []`: `node.Advance.spec`, the instance) takes nothing: a key it
     received stays in `rtkInv` with its tokens forever. **`run` needs nothing back but `np`, which is
     its own and which `advRet`/`RcvCommit` give back in both orders, whatever the driver holds.** So the
     instance is the traced proof at `ms = []` (A5).
   - A stale claim (a key `j` from an earlier `Ready` the driver advanced without it) is harmless:
     its bound `monoNatLb γn.al (j + 1)` still holds, its key is deposited, and the traced spec delivers
     its `ms`.
   - **Both orders against the Go** (`node.go` `run`, re-read for revision 2): `advancec` is set only in
     `case readyc <- rd:`, after `n.rn.acceptReady(rd)` returns (`:435-441`, `asyncStorageWrites`
     false), and `acceptReady`'s last statement is `traceReady` (`rawnode.go:437`); the loop head arms
     `readyc` again only when `advancec == nil` (`:354`), i.e. after `case <-advancec:` (`:443-446`)
     has run `n.rn.Advance(rd)` and cleared it. So `run`'s receive on `advancec` (the `RcvPending`
     offer, or its meeting of a `SndPending` driver) happens only between a key's deposit and the next
     key's allocation: `pend = false` there, which `np` makes a logical fact. The driver's send, in
     contrast, can be offered at any time after its `Ready` receive (it is the other goroutine): the
     `SndPending` case covers an offer made while `pend = true`, the `RcvPending` case one made after
     `run`'s offer. `Advance()` itself is a send on the unbuffered `advancec` or a receive on `done`
     (stopped: nothing taken, nothing owed).
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
| loop head: `n.rn.HasReady()`, `n.rn.readyWithoutAccept()` | `HasReady`, `readyWithoutAccept.spec` (one spec for both modes, slice 28n) | yes (re-opened by 1(a)-(e), §3.3) | `ownRawNode` |
| `case pm := <-propc: m.From = r.id; r.Step(m)` | `wp_rn_raft_Step_prop_traced` over `stepBundle_traced.onG PropAny` | yes (25n, 30c; re-opened, §3.3) | `PropAny`: `MsgProp`, non-empty, **normal entries** (`propP`; `fwdP`'s gated clause), `γ.reBoot ≠ []` (`trCapB_reBoot`). The bounds from the ceiling (below) |
| `case m := <-recvc` (guard: response from an unknown `From` → drop; else `r.Step(m)`) | `raft.Step.traced` (`raft.Step.tracedTriple`, slice 30c) | yes (re-opened, §3.3) | the token and `TrNetTy` from `netP` (5.); `StepNodeOk`'s `MsgAppResp` clause from the guard's `Progress` lookup; `MsgUnreachable` at term 0 (`UnreachPath`); `MsgHup` from `hupP`. The rest: §4 |
| `case cc := <-confc: r.applyConfChange(cc)` | traced `raft.applyConfChange` → traced `switchToConfig` | **no** (29n items 1-2) | the capability **booted** by 1(a): `DynCCPre` puts the entry inside the delivered log. `trCapB_hookGate_applyCC` (proved) at a follower; the leader excluded by 1(c), lemma (ii) and G3 (a) (§3.4); the result simple, 1(d) kept, by G3 (a) (the entry a bootstrap `AddNode`) |
| `case <-tickc: n.rn.Tick()` | `RawNode.Tick.traced` (26n) | yes (re-opened, §3.3) | `tickInv`'s credit; the bounds |
| `case readyc <- rd: n.rn.acceptReady(rd)` | `RawNode.acceptReady.spec` (one spec, 28n): fires the `Ready` line, post `[∗list] q ∈ ms, readyTok γ q.st` | yes (re-opened: `readyTok`'s body, 1(a) established, 1(b) by the emptied outbox; 1(c), 1(d) framed: B7, §3.3) | `ownRawNodeReady`; the escrow's allocation (with `al`) at the commit and deposit after (2.-3.) |
| `case <-advancec: n.rn.Advance(rd)` | traced `RawNode.Advance`: `stepsOnAdvance`'s self-addressed responses over `raft.Step.traced` with `pendingRel`'s `selfTok` (Q26 (a)); the storage acknowledgements over `stepBundle_traced_storAck` | **no** (designed in 28n, `AckEnd` done in 30c) | the self tokens from `pendingRel`'s `.self` arm; `TrNoSnap` makes the snapshot arm vacuous; `raft.Step.spec`'s traced `autoLeave` premise at `MsgStorageApplyResp` from 1(d); lemma (ii)'s `applied ≤ capplied` re-established (`advRS`'s `capplied := ca`). The handed-out tokens are already in `rtkInv` (3.) |
| `case c := <-status` | `getStatus` | yes (reads only) | — |
| `case <-stop: close(done)` | the stop protocol | yes | — |

**The bounds premises of the traced triples** (`uint.Z rs.tc + 1 < traceNumBound`, and
`receiptBound GF + γ.reBoot.length ≤ traceNumBound`): the first from `termLB γ.bud rs.tc` and
`budgetInv` (`rs.tc ≤ receiptBound GF`) with the cluster's `readyFits` (`receiptBound GF + 3 ≤ 2^61`);
the second is `readyFits` itself (`γ.reBoot.length = 3`). Read once per arm; no new invariant.

### 3.3 The RawNode triples `run` uses, and what the new clauses re-open (S5; revision 2, B7)

- **Proved, re-opened by `rnTrace`'s new clauses 1(a)-(e)** (each re-establishes `ownRawNode` at a new
  state, so each proof re-establishes the clauses; their statements do not change). They are re-opened
  in the landing that adds the clauses, after the clauses' facts are proved (§9, B1):
  - `RawNode.Tick.traced` (26n): (a) `delivered` unchanged; (b) its `raft.Step.traced`'s `OutTyStep`;
    (c) a campaign through `hup` (`HupCampaigns`' `¬ hasUnappliedConfChanges`, with §3.4's lemma (i));
    (d) the configuration unchanged (framed).
  - `RawNode.acceptReady.spec` (28n): (a) established here (the `Ready` line sets the flag before
    `delivered` grows); (b) the outbox emptied, and `TrScope` kept (it changes neither `lt` nor the read
    state's pending queues; it clears `readStates`, which `ReadIdle` does not read); (c) and (d) framed
    (it moves `applying`, not `applied`, and keeps the role and the configuration: B7); its post's
    `readyTok` body changes (§3.6), so it is re-opened for that too.
  - `RawNode.readyWithoutAccept.spec` (28n): reads only; frames the clauses.
  - `wp_rn_raft_Step_prop_traced` (25n) and the `raft.Step.traced` assembly (30c): (b) from the new
    `OutTyStep` conjunct (§3.6, L1, which re-opens the paths); (a), (d) frame (no step of a traced
    bundle changes the configuration); (c) `hup` as for `Tick`.
  - `stepBundle_traced_storAck` (30c), `stepBundle_traced_unreach` (27n): through the assembly.
- **Proved, unchanged:** `trCapB_hookGate_applyCC`, `traceConfChangeEvent.tracedSpec_proof` (29n).
- `RawNode.Step.traced`, `RawNode.Ready.traced`, `RawNode.ReportUnreachable.traced` exist but are not on
  `run`'s path (`run` calls `r.Step` and `acceptReady` directly); models for the `recvc` arm.
- **Not yet:** the traced `RawNode.Advance` (28n's design); the traced `raft.applyConfChange`,
  `raft.switchToConfig`, `RawNode.ApplyConfChange` (29n items 1-2); the traced `newRaft`,
  `NewRawNode`, `Bootstrap`, `setupNode` (§5).
- The alternative S5 offered (keep a clause only `run` reads in `run`'s own invariants) does not apply:
  1(a) needs the capability's flag, which only `rnTrace` sees; 1(b) and 1(c) change inside
  `raft.Step`; 1(d) is read inside the traced `RawNode.Advance` (its `raft.Step` premise). So the clauses
  go into `rnTrace` and the re-openings above are the cost.

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
  3. **Lemma (ii), the `confc` arm** (S7; revision 2, B3: the short form). An entry the `confc` arm
     applies sits at a position `k` with `k + 1 > raftLog.applied`. Stated as clause 1(e) of `rnTrace`
     (traced only; `CapOk`, `InvRawnode.lean:932`, already bounds `rs.capplied` by `committed`, the
     other way): `uint.nat s.logst.applied ≤ rs.capplied`. Then at the arm `DynCCPre` (`InvRawnode.lean:555-557`)
     gives `rs.capplied ≤ k`, so `applied ≤ k`, i.e. `k + 1 > applied` (positions are 0-based, log
     indices 1-based). Source of the clause: `raftLog.applied` moves only at `RawNode.Advance`
     (`MsgStorageApplyResp`'s `appliedTo`, sync mode), to the last index of the `Ready`'s committed
     entries, and the same `Advance`'s post sets `capplied := ca` (`advRS`, `InvRawnodeReady.lean:1344`;
     the call at `node__run.lean:1158-1160`), where `ca` is the driver's view after applying that
     `Ready` (`advanceP`'s `undecFree … ca` with `monoNatLbOwn γ.cam ca`; `confcP`'s `DynCCPreOp`
     gives the arm's `ca ≤ k` with `NoUndecConfIn`, `ApiVocab.lean:369-373`). **One check left**, for
     Probe B (§8): that `ca ≥` the `Ready`'s last committed index at `advanceP` (whether it is already
     in `ownRawNode` or follows from `Hca`); the `undecFree`/`cam` reading of revision 1 is not needed.
  4. **G3 (revision 2, A3): a joint invariant, (a) cluster-wide and (b) per node, each kept using the
     other.** At a traced cluster:
     - **(a) No configuration entry past the bootstrap log**: every entry of every log at a position
       `≥ |γ.reBoot|` has `¬ IsConfEnt e` (`CCModel.lean:65`: type `1` or `2`), fillers included.
       - *Owner*: the term logs' authority (the ghost map behind `isEntryR`, `Protocol/Ghost.lean`, where
         each entry is minted once by its term's leader and whose fragments every node's log carries
         through `logRecs`/`leadPrefix`: Log Matching). A gated pure clause of it:
         `γ.reTrace ≠ none → ∀ minted e at index i, i > |γ.reBoot| → ¬ IsConfEnt e`. Sealed, raft's.
       - *Established*: `cluster_alloc_traced` (nothing minted past the bootstrap log).
       - *Kept*: at each minting, the leader's appends in `raft.Step`'s code: a proposal's entries
         (`stepLeader`'s `MsgProp`, at a traced node under `raft.Step.spec`'s existing premise
         `MsgProp → s.gh.tr ≠ none → ∀ e ∈ ents, ¬ IsConfEnt e`, `raft__Step.lean:664`, which the
         traced callers discharge: `propP` (one normal entry), the gated `fwdP`); `becomeLeader`'s empty
         normal entry (`raft.go:961`); a refused conf change's empty normal replacement (`raft.go:1341`,
         not reached); and **`appliedTo`'s automatic leave** (`raft.go:742-761`), an empty
         `EntryConfChangeV2` stepped as a `MsgProp` from inside `raft.Step`'s `MsgStorageApplyResp`
         case: excluded at a traced node by `raft.Step.spec`'s existing premise
         `MsgStorageApplyResp → ents ≠ [] → c.autoLeave = true → s.gh.tr = none` (`:663`), which the
         traced `RawNode.Advance` discharges by (b). The minting update's statement gains the gated
         premise; its callers in the leader's append path pass the step's premise down (code proofs:
         `stepLeader`'s `MsgProp` branch and `becomeLeader`, to list at threading).
       - The registry route (revision 1's) is dropped: an empty `ConfChangeV2` is a filler
         (`Filler`, `Ghost.lean:1177`), with no ticket and no deposit, so the registry cannot see it.
     - **(b) No joint configuration**: clause 1(d) of `rnTrace`, `c.outgoing = ∅ ∧ c.autoLeave = false`,
       at every traced node.
       - *Established*: `setupNode`, after `Bootstrap`'s three `AddNode`s (`ConfChange` V1, whose `AsV2`
         never enters a joint configuration).
       - *Kept*: the configuration changes only in `switchToConfig` (the `confc` arm; `Bootstrap`) and
         at a snapshot's restore (no `MsgSnap` is ever sent at a traced cluster: §3.6). At the `confc`
         arm the entry is committed in the node's delivered log at a position `k`; by (a), `k <
         |γ.reBoot|`, so by lemma (i) it is a bootstrap `AddNode`, and the result is simple.
       - *Read*: the traced `RawNode.Advance` (the premise above) and §4's last row.
     - Induction over the cluster's steps: (a) at the pre-state of any step gives (b)'s preservation at
       a `confc` step; (b) at the leader gives (a)'s at an `Advance` step; other steps keep both
       locally. The two live apart because (a) is about every node's log (followers' entries are
       leaders') and (b) about one node's struct.
  5. From 1-4, the node is a follower at the `confc` arm: if not, `applied ≥ |γ.reBoot|` (1(c)) and
     `applied ≤ k` (lemma (ii)), while (a) puts the conf entry at `k < |γ.reBoot|`. So `AccIdle` and
     `SimIdle` apply.

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

### 3.6 The messages' types at the receiver (G1, G2; revision 2, A2)

`raft.Step.tracedTriple` needs `StepEndTy m.Type' ∨ AckTy m.Type'`, and the `propc` arm needs a
proposal's entries normal. At the `recvc` arm `netP` gives only `netStepTypes`; `fwdP` gives no entry
types. **No statement today supplies either fact.** The design:

- `TrSent st := TrNetTy st.msg.Type' ∨ (st.msg.Type' = MsgProp ∧ ∀ e ∈ st.ents, e.Type' = EntryNormal)`.
- **At the sender**: `acceptReady`'s tokens `readyTok γ q.st` become `⌜TrSent q.st⌝ ∗ recvTokOf …`;
  they go through `rtkInv` to the driver as `trTok` (same body). `acceptReady` proves `TrSent q.st` for
  each handed-out `q` from `outboxRelP` (`msgAbs q.st a`): if `a = some x`, `x ∈ s.outbox` and
  `rnTrace` 1(b) gives `TrOutMsg x` (below), which `msgAbs` turns into `TrSent q.st` (the abstract type
  is `mtypeOf` of the physical one; a `propose`'s entries are the message's); if `a = none` (a type
  without abstraction), `XfOk`'s new clause refutes it (the physical half, below).
- **Through the client**: `stepIn_intro` takes `trTok` (with `TrSent`) into the gated `stepP`: a
  `MsgProp` to `fwdP` (normal entries), anything else to `netP` (`TrNetTy` with the token).
- **The type list, against the Go** (unchanged from revision 1). The handed-out messages are `r.msgs`
  and the `msgsAfterAppend` not to self (`rawnode.go:145`, `:179-183`; the self ones go to
  `stepsOnAdvance`, `:414-417`). Their types at a traced node: `MsgApp`, `MsgHeartbeat` (leader),
  `MsgVote` (candidate), the three responses (`TrNetTy`), and a follower's forwarded `MsgProp` (normal
  entries, by `PropAny`). Excluded: `MsgReadIndexResp` (only from a pending read: `ReadIdle`),
  `MsgTimeoutNow` (`lt ≠ 0`), `MsgSnap` (`maybeSendSnapshot` only after compaction, which `TrNoSnap`
  refutes at `maybeSendAppend`'s two fallbacks, `raft__maybeSendAppend.lean:121-124, 431-434`; and
  `raft.send.spec`'s traced premise `mtypeOf m.Type' ≠ some .snap`: revision 2 cites these, not
  `ReplSends`, whose `.snap` exclusion needs the no-snapshot mode, off at raft's level), pre-votes
  (`prevote = false`), forwarded `MsgReadIndex`/`MsgTransferLeader` (only from stepping those types,
  which `StepEndTy` excludes), storage messages (`AsyncStorageWrites = false`: `:163-173` not taken).
  `TrScope` is kept: only `MsgReadIndex` adds a read and only `MsgTransferLeader` sets `lt`, both
  excluded; `becomeX` resets `lt`.

**The abstract half: `OutTyStep`, in `stepBundle_traced.statement`'s post (A2).** In
`StepGhostMode.lean`, next to `OutTrStep`:
```lean
def TrScope (s : NState) : Prop := s.lt = W64 0 ∧ ReadIdle s
def TrOutMsg (m : Msg) : Prop :=
  m.ty.traced = true ∨ (m.ty = .propose ∧ ∀ e ∈ m.entries, e.Type' = EntryNormal)
/-- A traced step in scope stays in scope and queues only traced types or normal proposals. -/
def OutTyStep (s s' : NState) : Prop :=
  s.gh.tr.isSome → TrScope s → TrScope s' ∧ ∀ m ∈ s'.outbox, m ∈ s.outbox ∨ TrOutMsg m
theorem OutTyStep.of_none (h : s.gh.tr = none) : OutTyStep s s'
```
- **Where it goes: the caller's end resource, not `stepClose`'s definition.** `stepBundle_traced.statement`
  (and `.on`/`.onG`/`.onA`, the per-path forms, `TracedRaftStep.lean`) end with
  `stepClose γ md c id m ents ctx s R Gout` at `Gout s' := ∃ bt', trCapB … (SimIdle C s') (stepLastEv Λ)`.
  Revision 2 makes it `Gout s' := (∃ bt', trCapB …) ∗ ⌜OutTyStep s s'⌝`. `raft.Step`'s code proof
  returns `Gout s'` untouched (it is the caller's), so `raft__Step/*.lean` and `LemmasStepGates.lean`'s
  `stepClose`/`stepCloseAt` do not change; `raft.Step.tracedTriple`'s post, which hands back the
  capability through `Gout`, now also gives `⌜OutTyStep s s'⌝`, and so do `RawNode.Tick.traced` and
  `wp_rn_raft_Step_prop_traced`, which call it. `stepClose_anyB` (its `Gout` is the capability alone)
  gains the pure conjunct in its statement (one line).
- **Each path proves it at its close** from the state it closes at (`StepEnd`'s `s'` and the messages
  it queued, which it knows: it built their gates): the vote paths queue a `MsgVoteResp`; a candidate's
  campaign `MsgVote`s; the append paths a `MsgAppResp`; the heartbeat paths a `MsgHeartbeatResp` (and
  no `MsgReadIndexResp`: `ReadIdle`); a leader's accepted `MsgAppResp` `MsgApp`s (the snapshot fallback
  refuted by `TrNoSnap`, no `MsgTimeoutNow` since `lt = 0`); a leader's proposal `MsgApp`s; a
  follower's proposal the forwarded `MsgProp` with `PropAny`'s normal entries; `MsgBeat`
  `MsgHeartbeat`s; `MsgHup` the campaign's `MsgVote`s; a stale message's `LowSend` response (`TrNetTy`);
  `MsgUnreachable` and the storage acknowledgements' paths queue `MsgApp`s at most. Untraced, or out of
  scope, vacuous.
- **The files it re-opens** (the 30c assembly's paths, planned work, not a blocker): the statement and
  assembly, `TracedRaftStep.lean`, `TracedRaftStepBundle.lean` (`raft.Step.tracedTriple`,
  `stepBundle_traced`, `stepBundle_traced_storAck`), `TracedRaftStepPaths.lean`; the paths,
  `TracedRaftStepHup.lean`, `TracedRaftStepLocal.lean`, `TracedRaftStepPropBundle.lean`,
  `TracedRaftStepUnreach.lean`, `TracedRaftStepRecv.lean`, `TracedRaftStepRecvApp.lean`,
  `TracedRaftStepRecvAppAccCand.lean`, `TracedRaftStepRecvAppAccFol.lean`,
  `TracedRaftStepRecvAppAccUT.lean`, `TracedRaftStepRecvAppRej.lean`, `TracedRaftStepRecvCand.lean`,
  `TracedRaftStepRecvCandApp.lean`, `TracedRaftStepRecvHb.lean`, `TracedRaftStepRecvLeadAccBundle.lean`,
  `TracedRaftStepRecvLeadAccGates.lean`, `TracedRaftStepRecvLeadNA.lean`, `TracedRaftStepRecvLeadReq.lean`,
  `TracedRaftStepRecvLeadSend.lean`, `TracedRaftStepRecvUTApp.lean`, `TracedRaftStepRecvUTHb.lean`,
  `TracedRaftStepRecvUTResp.lean`, `TracedRaftStepRecvUTVote.lean`, `TracedRaftStepRecvUTVoteResp.lean`,
  `TracedRaftStepRecvVoteResp.lean`, `TracedRaftStepRecvVoteRespWon.lean`,
  `TracedRaftStepRecvVoteRespLost.lean`, and the close helpers of `TracedPin.lean` (27 files); their
  consumers, which pass `Gout` through, `TracedNodeRecv.lean`, `TracedRawNode.lean`,
  `TracedRawNodeRep.lean`, `InvRawnode.lean` (4). No statement outside raft's internals changes.

**The physical half (found in revision 2).** `msgAbs q.st none` holds of a message whose type has no
abstraction (`mtypeOf … = none`), and `absList` drops it: **no conjunct on the abstract outbox can
exclude it**. Of the types raft queues (`XfOk`'s `SentMsgShape`: `sentShapeTypes`), two have none:
`MsgTimeoutNow` (`sendTimeoutNow`: `stepLeader`'s `MsgTransferLeader` case, and its `MsgAppResp` case
when `m.From == r.leadTransferee`) and a forwarded `MsgTransferLeader` (`stepFollower`). Neither is
queued at a traced node in Go (no transfer is stepped: refused, `TrNetTy`; `lt` stays `0` and a
`MsgAppResp`'s sender is non-zero, `raft.Step.spec`'s premise). The design, in raft's code specs, in
the style of the traced premises they already have (`raft__Step.lean:659-664`):
- `raft.send.spec`'s traced premise `s.gh.tr ≠ none → mtypeOf m.Type' ≠ some .snap` becomes
  `s.gh.tr ≠ none → ∃ ty, mtypeOf m.Type' = some ty ∧ ty ≠ .snap`;
- `XfOk id s l` (`InvRaftPhys.lean:426`) gains the clause `s.gh.tr.isSome → ∀ q ∈ l, mtypeOf
  q.st.msg.Type' ≠ none`, which `raft.send`'s proof keeps from that premise and `acceptReady` reads;
- `raft.sendTimeoutNow.spec` gains `s.gh.tr = none`; `raft.Step.spec` gains `m.Type' =
  MsgTransferLeader → s.gh.tr = none` and `s.gh.tr ≠ none → s.lt = W64 0`, passed to `stepLeader.spec`
  / `stepFollower.spec`, whose transfer branches and the `From == leadTransferee` branch (`From ≠ 0`)
  discharge `sendTimeoutNow`'s and `send`'s premises;
- `raft.Step.tracedTriple` discharges the two by `StepEndTy` and a new premise `s.lt = W64 0`, which
  `run`'s arms, `RawNode.Tick.traced` and the traced `RawNode.Advance` read from `rnTrace` 1(b)'s
  `TrScope`; every untraced caller of `raft.Step.spec` has `s.gh.tr = none`.
Files: `Spec/go_etcd_io/raft/v3/{raft__send,raft__sendTimeoutNow,raft__Step,stepLeader,stepFollower}.lean`
and their proofs, `InvRaftPhys.lean`, `TracedRaftStepBundle.lean`, and the callers of `raft.Step.spec`
(each untraced: the extra premises by `s.gh.tr = none`). Lands with L1 (§9).

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
| (`raft.Step.tracedTriple`) `MsgStorageAppendResp → sn = none`; `MsgStorageApplyResp → ents ≠ [] → c.autoLeave = false` | no snapshot (`TrNoSnap`, in its update form, A4); no joint configuration: `rnTrace` 1(d) (G3 (b), §3.4 item 4) | `setupNode` (L5 closed); G3 |
| (revision 2, A2's physical half) `s.lt = W64 0` | `rnTrace` 1(b)'s `TrScope` | §3.6 |

Every row but G1, G2 (and G3 behind one of them) cites a fact that exists today; G1 and G2 are
§3.6's `OutTyStep` and physical half, G3 §3.4 item 4.

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
- **`NewRawNode`/`setupNode` traced**: thread these. After `Bootstrap`, `simIdle_boot` (slice 21; on
  branch `trace-check-a8` it takes `id ∈ C`, which `Φvs` and the voter's `nodeBoot` give) gives the
  phase `SimIdle C s`. `setupNode` mints `bootDone tn id` by `trCapB_bootDone` (A8.2) at
  `Λend`: its `hΛ` holds since `Φvs C _ _` gives `C = vs`, so `Λend o` is `BootEvAt C id (C.length + 3)`.
  It then packs `rnTrace` (weakening `Λend` to the default `Λ`, the phase `Φvs` to `SimIdle`) with:
  - **`TrNoSnap` (revision 2, A4; L5 closed)**, in its update form
    `TrNoSnap tr ls := □ (⌜tr ≠ none⌝ -∗ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) -∗ |={⊤}=> False)`
    (`TracedSend.lean`; `trNoSnap_traced` concludes `… -∗ |={⊤}=> False`; `trNoSnap_none`,
    `trNoSnap_congr`, `rnTrace_congr` keep their proofs). Built here at the fresh log state: its
    `prev.index` is `0` (a fresh `MemoryStorage`'s `FirstIndex` is `1`), refuting the first disjunct
    purely; for the second, `storPast st 1` is `∃ n ≥ 1, storCompacted st n.toNat`, and the client's
    `isStorage γ K st` (persistent, captured by the wand) has `"#Hbound" : □ (∀ c, storCompacted st c
    ={⊤}=∗ storBnd γ K c)` (`InvStorage.lean:282`), whose gated conjunct `⌜c = 0 ∨ Cluster.trace γ =
    none⌝` (Q6 item 8) refutes `c ≥ 1` at a traced cluster. It is built from the client's contract
    before `storBnd_raftBnd` (`StartNode.lean:107`) converts it to raft's `raftBnd`, so `raftBnd` needs
    no gate (the conversion drops the conjunct: one more `-` in its `icases`). The two uses
    (`raft__maybeSendAppend.lean:121-124, 431-434`) are WP steps of `raft.maybeSendAppend.spec`'s proof,
    a plain triple at `⊤` with no invariant open: `iapply trNoSnap_traced …` becomes
    `imod (trNoSnap_traced …) with []`. The other files mentioning `TrNoSnap` (25 in all) pass it by
    name: no statement changes.
  - **1(b)'s `TrScope`** (`lt = 0`, no pending read, the outbox empty) and **1(d)** (after the three
    `AddNode`s, the configuration simple) hold of the fresh node; 1(a) (nothing delivered) and 1(c) (a
    follower) trivially; lemma (ii)'s `applied ≤ capplied` at `0 ≤ 0`.
  - The node's escrow `rtkInv` (§3.2, 2.), with `al` and `dep` at `0` and `np` given to `run`.
- **`StartNode.gatedSpec`** (A8.3) from `setupNode` and `run`'s spawn (`node.run` at a traced node: §9's
  order, `node.run.gated_of` then the dropped premise).

### 5.3 Amendment A8 (Q36 (a), Q37 (a), decided by the coordinator): exact statements

**Revision 2: as implemented** (branch `trace-check-a8`, `84dd5b2e36`..`65a42909a1`; reviews `a8-r1.md`,
no first-tier finding, and `a8-r2.md`; `notes/decisions.md`, "Amendment A8 (Q36, Q37)"). The statements
below are revision 1's, amended where the implementation differs; where they differ, the branch's are
the design's:
- **The witness is a mono list, not a ghost map**: `bootDone tn i := ∃ k, monoListIdxOwn tn.dn k i`
  (persistent), `simInv`'s clause `∃ Dn : List w64, monoListAuthOwn tn.dn 1 Dn ∗ ⌜∀ i ∈ Dn, BootDone C L i⌝`.
  A ghost map's authority cannot hand out a second element for a key already present, so a second
  minting for one node would need a premise the capability does not carry; a mono list's authority gives
  an index witness of any member, and `trCapB_bootDone` appends `id` unconditionally.
  `Cluster.traceSimInv_alloc`/`traceSim_alloc` take `monoListAuthOwn tn.dn 1 []`.
- **`bootInit` is deleted**, not kept beside an equation (review a8-r1; raft's `InvBoot.bootInit` has the
  name), with `bootInit_eq`, `bootInit_ne_simInit`, `not_bootFacts` and the unused `simInv_end_boot`;
  A7's `newTrace_bootInit` is **`newTrace_simInit`** (concluding `t.init = simInit C`), and
  `bootFacts_of_bootDone` states positively that complete segments give `BootFacts`.
- `simInit_s_voter` and **`simInit_s_nonvoter`** (`= bootJunk`) are the two cases. The readers that
  stated a voter's fact of every id gain a membership premise (`simInit_log`, `srvFacts_simInit`,
  `simIdle_boot`: `i ∈ confAbs C` / `j ∈ C` / `id ∈ C`; every caller has it); the others split on the
  case, the fact holding of `bootJunk` too. **B1.4 is met**: every reader under
  `tracecheck_Events_traceAccepts` (`TraceSimRun`, `TraceSimMatch`, `MainSim`, `TracedNodeBoot`) was
  re-proved in that landing or compiled unchanged (`SimRun` and its first step), none as a `sorry`.
- `trCapB_bootDone` is the abbrev `trCapB_bootDone.statement` (`TracedCap.lean`), proved in
  `TracedHooksGlobal.lean`, its conclusion `trCapB … ⊢ |={E}=> (trCapB … ∗ ∃ tn, traceDir γd tn ∗
  bootDone tn id)`; the clause is kept by every law through `bootDone_snoc` (`trCapB_perm` included).
- `HarnessEnd.lean`'s hypothesis `BootEnd D` is now the **theorem `bootEnd`**, over `nodeBoot`,
  `traceDir γd tn`, `Cluster.traceSim`, `□ [∗list] i ∈ vs, startDone γ i` and `traceAuth`, with `htr`,
  `hne`, `hlen`; `runOk_at_end` and `runOver_intro` take the same (§2.2's last row).
- Not done there: the minting at the end of `setupNode` (§5.2), which waits on the traced
  `newRaft`/`Bootstrap`.

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
- **The harness's own calls**: `proto.ClonePb.wp_proof` (`proto.Clone` of a message, at `pbMessage`,
  whose decoder `msgDecode` is an `opaque`, not an axiom; the module moves to raft's tree, B4, which
  changes no axiom); `proto.UnmarshalConfChange.wp_proof`, `proto.UnmarshalConfChangeV2.wp_proof`
  (the `ConfChangeV2` arm, A6), `ccDecodeV2_nil` (an empty `ConfChangeV2` decodes) and
  `strconv.Itoa.wp_proof` (all already above).
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
- **Thread tokens** (revision 2, B5): `RunConcurrent` forks each `app` by `wp_fork_tok_body`
  (`Perennial/GooseLang/Lifting.lean`), handing it the fork's fresh `threadTok`; `app`'s loop invariant
  holds one token; it deposits it at each `Add` (`netJoin.wp_Add`), the `go` gives it a fresh one
  (`wp_fork_tok_self`), and the message goroutine ends with the token `netJoin.wp_Done` hands back;
  `app` returns its token at `c.stop`. The other goroutines `RunConcurrent` forks use `wp_fork`.
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
redone for a changed sealed body (§3.3). Revision 2: rows re-checked against A1-A6 and B1-B7; changed
rows say so.

| Statement | Proved from (callee statements) | Why it suffices |
|---|---|---|
| `raft_tracecheck_safe` (§1.2) | `tracecheck_adequate_of` (new binders; `Hn : n + 2 ≤ 2^31`), `tcMainSpec` | adequacy turns `Main`'s spec at every `HeapGS` into the operational statement; the instance and `Hbound` from `HT`/`HN` (§6); `Hprem` at each `hG`, as putget |
| `raft_tracecheck_accepts` (§1.3) | `RunConcurrent.spec` at `defaultCConfig` (`Workload` by `decide`) under the instance, `tracecheck_Events_traceAccepts` | the post `runOver c` is the latter's precondition |
| `tcMainSpec` / `Main.spec` ★(premises) | `Main.wp_proof` (proved) with `RunConcurrent.spec` and the checker's Link | unchanged proof, plus passing the instance and `premises boot` |
| `RunConcurrent.spec` ★ | §2.2's calls: `harness_alloc`, `tcOpsInv` (with its requested-entries clause, A6)/`confPolicy_alloc`/`tcSnapsInv`, the storage with `storBnd_zero` (B2), `startTraceC_intro`, `StartNode.tracedSpec`, `sync.join`, `join3`, `netJoin`, `wp_fork_tok_body` for `app` (B5), `app`/`send`, `node.Stop.spec`, `time.Now`, `Time.Add`, `runOver_intro` (with `bootEnd`, a theorem on `trace-check-a8`) | allocation gives each voter's `startTraceC`; the three `startDone`s with `traceDir` and `Cluster.traceSim` give `BootFacts`; `runOver_intro` composes |
| `app` ★ (harness-local: `isNode`, driver state, `nodeRunning 1`, `njAdder ⅓`, `ownDone apps …`, a `threadTok`) | `time.NewTicker`, `node.Tick.spec`, `isReadyChan_recvAu.tracedSpec`, `handleReady`, `node.Advance.tracedSpec`, `proto.ClonePb.spec` at `pbMessage` (moved to raft's tree, B4), `send`, `wp_fork_tok_self` | loop invariant: the driver idle, `nodeRunning 1`, `njAdder ⅓`, one `threadTok` (B5). Each round: the claim (with its allocation bound, A1) at the receive, the tokens at `Advance`, one `send` per token |
| `handleReady` ★ | storage contract, `tc_confShaped` (`tcOpsInv`, `ownCommittedOps_lb_prefix`, `confShaped_of_ops` moved to `ConfRule.lean`), `proto.UnmarshalConfChange.spec`, `proto.UnmarshalConfChangeV2.spec`, `confPolicy_decide`, `committed_emptyV2_joint`, `node.ApplyConfChange.spec`, `snapshotCert_made`, `snapMade_elem` with `tcSnapsInv` | **changed (A6)**: both conf arms as kvreconf's `Replica__applyEntry`, from client-visible facts only (§2.3); the snapshot branch refuted from `readySnap` |
| `send` ★ | `netJoin.wp_Add`, `wp_fork_tok_self`, `trTok_type`, `node.Step.tracedSpec`, `node.ReportUnreachable.spec`, `netJoin.wp_Done` | the token rides into the goroutine; `ReportSnapshot` dead by `trTok_type`; the goroutine ends with `wp_Done`'s thread token |
| `netJoin` laws, `join3` ★ | raw `WaitGroup.Add/Done/Wait`, `alloc_wait_token`, `threadToks_add_one_lt`, `ThreadBoundLe.le` | §6, end to end |
| `StartNode.tracedSpec` ★ (A8.3) | `StartNode.gatedSpec` (Draft, amended), `startTraceC_eq` | the Draft's over the sealed names (as today's `tracedSpec_of_gated`) |
| `StartNode.gatedSpec` ★ | `setupNode` traced, `node.run.gated_of` then `node.run.spec` (§9's order) | `setupNode` returns the node with `bootDone`, `rtkInv` and `runPre`; `go n.run()` |
| `setupNode`/`NewRawNode` traced ★ | `newRaft.tracedSpec`, `RawNode.Bootstrap` traced, `trCapB_bootDone`, `simIdle_boot` (with `id ∈ C`), the client's `isStorage` at the gated `storBnd` (for `TrNoSnap`, A4) | §5.2: `rnTrace` with 1(a)-(e), `TrNoSnap` in its update form, the escrow (L5 closed) |
| `newRaft.tracedSpec` ★ | `startTrace_trCapB` (proved, at `cC`), `trCapB_hookGate_init`/`_ccBoot` (proved), traced `traceConfChangeEvent.spec` ★ (`RaftReadLend`), `raft.becomeFollower.traced` (proved) | positions 0-2 by `BootNext` from each previous `Λ` and `Φvs` |
| `RawNode.Bootstrap` traced ★ | `raft.becomeFollower.traced`, `bootMarshal`, traced `raft.applyConfChange` ★ (follower, `_ccBoot`) | positions 3 to `|C| + 3` |
| `trCapB_bootDone` (A8.2) | `simInv`'s `Bt`/`LastOf`/`BootSegs`, `bootEvAt_unique`, `bootDone_of_last` | proved on `trace-check-a8` (§5.3) |
| `Cluster.traceSim_bootEnd` (A8.4) | `traceDir_agree`, `simInv`'s `Dn` clause, `Cluster.traceSimInv_bootEnd`, `simInv_end_bootDone`, `newTrace_simInit` | proved on `trace-check-a8` (§5.3) |
| `isReadyChan_recvAu.tracedSpec` ★ (revised) | `isReadyChan`'s protocol with `readyP` carrying the escrow element and `monoNatLb γn.al (j + 1)` (A1) | both are minted at `run`'s `readyc` commit (§3.2, 3.) |
| `isReadyChan_recvAu` (untraced law) | re-opened: `readyP`'s gated element is dropped | holds for every `γ` |
| `node.Advance.tracedSpec` ★ (the one proof, A5) | `advInv` with `np` lent and the `SndPending` payload's allocation bound (§3.2, 4.), `rtkInv` | **changed (A1)**: `pend = false` at `run`'s side of the rendezvous in both orders; in `RcvPending` the driver's element gives `j < a`, in `SndPending` the payload's `monoNatLb γn.al (j + 1)` does, and `run` answers `monoNatLb γn.dep (j + 1)`; stale keys too; `ms = []` takes nothing |
| `node.Advance.spec` | **its instance** (`node.Advance.spec_of_traced`, `readyToksClaim_nil`); text unchanged, every `γ` (A5) | no second proof |
| `node.Step.tracedSpec` (corollary) | `stepIn_intro` (with `trTok`), `node.Step.spec` | — |
| `node.Step.spec` | proof unchanged (`stepWithWaitOption` passes `stepP`) | every `γ` |
| `stepIn_intro` (gains `trTok`) | re-opened: `ApiImpl.stepIn_intro_impl` splits on the trace | §3.2 items 5-6 |
| `trTok_type`, `trTok_untraced` | `trTok`'s body (`TrSent`) | — |
| the five refused `node.X.spec`s (§3.5) | their proofs plus the premise discharging `netP`'s/`stepP`'s untraced arm (`ProposeConfChange`: its internal `stepIn`) | untraced `netP`/`fwdP` unchanged |
| `node.run.gated_of` ★ (one spec at the end) | §3.2's arms: `raft.Step.traced` with `stepBundle_traced` (re-opened), `wp_rn_raft_Step_prop_traced` (re-opened), `RawNode.Tick.traced` (re-opened), `acceptReady.spec` (re-opened), `readyWithoutAccept.spec` (re-opened), traced `RawNode.Advance` ★ (`hAdv`), traced `raft.applyConfChange` ★ (`hCC`, follower case), lemmas (i), (ii), G3 (a), `getStatus`, `rtkInv` | the invariants of §3.2 (1.-6.) give each arm's premises (§4); the leader excluded at `confc` (§3.4 item 5); the bounds by the budget. Stated only after L1, (i), (ii), G3 and `TrNoSnap`'s form are theorems (B1.5), so its hypotheses are `hAdv` and `hCC` only |
| traced `RawNode.Advance` ★ | `raft.Step.traced` (self responses: `TrNetTy`, `selfTok`), `stepBundle_traced` on `AckTy` (`.onA`, `stepBundle_traced_storAck`), `TrNoSnap` (update form: an `imod`), `rnTrace` 1(d) (the `autoLeave` premise) and 1(b) (`s.lt = 0`) | 28n's design; `stepsOnAdvance` holds exactly the self responses and the two acknowledgements (`rawnode.go:411-426`); re-establishes lemma (ii) (`advRS`) |
| traced `raft.applyConfChange` / `switchToConfig` ★ | `Changer` specs giving back the old maps, `traceConfChangeEvent.spec` over `RaftReadLend` ★, `trCapB_hookGate_applyCC` (proved, booted) / `_ccBoot` (unbooted) | follower case argued (29n); the leader excluded (§3.4 item 5); 1(d) kept by G3 (a) |
| `rnTrace`'s new clauses 1(a)-(e) ★ | established at `setupNode`; kept by the re-opened triples of §3.3 | added after their facts (§9's order): 1(b) by `OutTyStep` (§3.6), 1(c) by lemma (i), 1(d) by G3 (a) |
| `OutTyStep` in `stepBundle_traced.statement`'s `Gout` ★ (A2) | each path's close (the 27 files of §3.6) | each path knows what it queued |
| the physical half: the traced premises of `raft.send.spec`, `raft.Step.spec`, `raft.sendTimeoutNow.spec`; `XfOk`'s clause ★ (A2) | `stepLeader`/`stepFollower`'s transfer branches; `raft.Step.tracedTriple`'s `StepEndTy` and `s.lt = 0` | §3.6 |
| G3 (a), the term logs' gated clause ★ (A3) | `cluster_alloc_traced`; the minting update's new premise, from `raft.Step.spec`'s traced `MsgProp` premise and its `autoLeave` premise (1(d)) | §3.4 item 4 |
| lemma (ii), `applied ≤ capplied` ★ (B3) | `RawNode.Advance`'s `advRS`; one check for Probe B | §3.4 item 3 |
| `raft.Step.traced`, `stepBundle_traced` | proved (30c); re-opened for `OutTyStep` (A2) and the physical half's premise | — |
| `TrNoSnap`'s update form (A4) | `trNoSnap_traced`'s new conclusion; `raft__maybeSendAppend.lean`'s two refutations by `imod` | §5.2 |
| `storBnd`'s gate; `storBnd_zero`, `storBnd_intro_untraced` (B2) | — | the three kv-family lemmas and `memStorage_isStorage` re-proved through them (§9, L3) |
| `trCapB_hookGate_applyCC`, `traceConfChangeEvent.tracedSpec_proof`, `startTrace_trCapB`, `cluster_alloc_traced`, `harness_alloc`, `Cluster.traceSim_alloc`/`_end`, `tracecheck_Events_traceAccepts`, the checker's Link, `confPolicy_alloc`/`_decide`, `snapshotCert_made`, `snapMade_elem` | proved | — |
| `runOver_intro`, `runOk_at_end` (`HarnessEnd`) | restated over `startDone` (S3); proofs: `Cluster.traceSim_bootEnd` in place of `HD` | — |
| the fire laws, `trCapB_perm`, `Cluster.traceSimInv_alloc` | re-opened for `simInv`'s `Dn` (A8.2) | statements unchanged |

---

## 8. The end-to-end probe (after review)

**The path, in the Go's order**: `StartNode`, `Ready`, `handleReady`, `Advance`, then `send`→`Step`.

The first `Ready` of a fresh voter hands out no message, so the concrete run that reaches a message:
`StartNode` ×3; voter 1's first `Ready` (the three bootstrap entries; `ApplyConfChange` ×3 through
`tc_confShaped` and `confPolicy_decide`; `Advance` without using the claim's tokens: `ms = []`); ticks
until `tickElection` campaigns (`hup`: `applied = 3 ≥ |boot|`, §3.4); voter 1's second `Ready` with
`MsgVote` to 2 and 3 (key 1 of voter 1's escrow); `Advance`, giving `trTok` for each `MsgVote`;
`proto.Clone`; `send` → `node.Step` at voter 2; voter 2's `recvc` arm steps the `MsgVote` (`TrNetTy`)
and logs the receive line after voter 1's `Ready` line.

**Probe A (client glue, harness level; easy).** A Lean `example` over the client statements as
hypotheses:
- `harness_alloc`, `tcOpsInv` (with its requested-entries clause)/`confPolicy_alloc`/`tcSnapsInv`, the
  storage with `storBnd_zero`, then `startTraceC_intro`;
- `StartNode.tracedSpec` (A8.3, as on `trace-check-a8`) for one voter;
- the fork of `app` by `wp_fork_tok_body` (B5): `app`'s precondition with its `threadTok`;
- `isReadyChan_recvAu.tracedSpec` (revised), giving `readyGotT` with the claim on `ms`;
- `handleReady`'s refutation of a snapshot `Ready` (`snapshotCert_made`, `snapMade_elem`), and (A6)
  its `ConfChangeV2` arm: `tc_confShaped`, `proto.UnmarshalConfChangeV2.spec` without error,
  `committed_emptyV2_joint`, `confPolicy_decide`, `node.ApplyConfChange.spec`'s premises;
- `node.Advance.tracedSpec`, giving `[∗list] q ∈ ms, trTok γ q.st`; and `node.Advance.spec_of_traced`
  (A5);
- for `q ∈ ms`: `netJoin.wp_Add` with the thread token, `wp_fork_tok_self`, `proto.ClonePb.spec` at
  `pbMessage` (imported from raft's tree, B4), `trTok_type`, then `stepIn_intro` (with `trTok`) and
  `node.Step.spec` at `q.msg.To'`, and `netJoin.wp_Done` giving the goroutine's token back;
- at the end, `bootEnd` (`Cluster.traceSim_bootEnd`) with the three `startDone`s and `traceDir`, then
  `runOver_intro`.

It checks that each post supplies the next pre: the claim's `ms` against `readyGot`'s `ms` and
`rd.Messages`; `ClonePb`'s `T.ro` from the `Ready`'s `msgOwn … (readyDq q.st)` and its `T.dec`/`eqv`
into `msgPtsC … ⟨…, []⟩` (S1's correction); `trTok` against `stepIn_intro`'s `st`; `app`'s token
through each round; the `ConfChangeV2` arm's `Membership.applyChange` from `m.isJoint`; `startDone`
into the end law.

**Probe B (node level; hard, chosen by its invariant).** The new invariant is the escrow `rtkInv` with
`run`'s lent `np` and the allocation bound (§3.2, 2.-4.), plus `stepP`'s gated token and type (§3.6).
Prove, for one node:
1. `run`'s `readyc` arm: the key allocated (`pend := true`, `np` in, `al` raised, its lower bound
   minted) and the element with the bound into `readyP`; then `acceptReady.spec` (its `"Htoks"`) and
   the deposit (`np` out, `pend := false`, the `readyTok`s into `trTok`-bodied slots).
2. The busy loop state with `np`.
3. The `advancec` rendezvous in both orders: `RcvPending` (the driver's commit with `np` in `advDep`,
   its element giving `j < a`), and **`SndPending` with the payload's `monoNatLb γn.al (j + 1)`** (A1),
   offered while `pend = true`, `run`'s commit minting `monoNatLb γn.dep (j + 1)` and the driver's
   later swap with `pend = true` again for a newer key; yielding `node.Advance.tracedSpec`'s tokens; the
   same with the claim's left disjunct `ms = []` (`node.Advance.spec`'s instance), which must leave
   `run` with `np` and nothing else owed; and with a **stale** claim. Each opening of `rtkInv` inside a
   channel AU at `⊤ ∖ ↑(that channel's namespace)` (B6).
4. At the receiver, `stepIn_intro`'s traced split into `netP`/`fwdP`, then the `recvc` arm through the
   guard to `raft.Step.traced` with `StepNodeOk` and the token.
5. (B3) Lemma (ii)'s one check: at `RawNode.Advance`, the driver's `ca` (from `advanceP`) is at least
   the `Ready`'s last committed index, so `advRS` re-establishes `applied ≤ capplied`.

The riskiest piece: it checks that the instance at `ms = []` is provable at a traced node (F3, A5),
that the deposit is found in both orders (A1), and that `rnTrace` 1(b) with `XfOk`'s new clause gives
`TrSent` at `acceptReady` (G1's sender half, A2).

---

## 9. Links not argued, the order of work, and decisions

**Links I could not argue in full** (all raft-internal; none touches §1):
- **L1, narrowed (A2).** The type list holds of the Go (§3.6) and the obligation is placed:
  `OutTyStep` in `stepBundle_traced.statement`'s `Gout`, each path proving it at its close, plus the
  physical half. **Not checked:** that a broadcasting path (a leader's accepted `MsgAppResp`, a
  leader's proposal, `MsgBeat`, the storage acknowledgements) sees the types of its queued messages at
  its close. `StepEnd` gives them only as `ReplSends`' existential messages, which admit `.snap`; the
  path must carry the types from the send gates it fired (`sendOutGate id s c m.Type' out`, one per
  queued message, at a traced node never with a snapshot by `raft.send.spec`'s traced premise) into
  the resource its close reads. If a gate's traced body does not record the type, it gains it (the
  send hook's gate, raft-internal). To settle in the first path re-opened
  (`TracedRaftStepRecvLeadAccBundle.lean`).
- **L2 (§3.4), the leader exclusion.** Lemma (i) argued; lemma (ii) in the short form, one check left
  (Probe B item 5); **G3** argued as a joint invariant (§3.4 item 4). Not located yet: the term logs'
  minting update and the code proofs that call it (`stepLeader`'s `MsgProp` branch, `becomeLeader`),
  which pass `raft.Step.spec`'s traced `MsgProp` premise down; listed at threading. Fallback: 29n's
  leader line lemma.
- **L3 (§3.5, F2, F3; revision 2, B2). The client call sites, counted** (by the Go call or the lemma
  applying the spec; `RaftWitness` excluded, it has its own raft; links that only pass `wp_node_X`
  through not counted):
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
  - **`storBnd` (B2, new)**: 4. Three client lemmas unfold it: kv's `kvJ_bnd`
    (`kv/KVStorageInstance.lean:273-275`), kvreconf's `kvrJ_bnd` (`kvreconf/KvrStorageApi.lean:274-276`),
    kvdurable's `kdJ_bnd` (`kvdurable/KdStorageApi.lean:147-149`); each is re-proved through the new
    exported `storBnd_intro_untraced : Cluster.trace γ = none → nodeAppliedLb γ K k -∗ ⌜c ≤ k⌝ -∗
    storBnd γ K c` (no unfold) and gains that premise, which its caller has from its cluster's
    `%Htr0` (kv: at its storage's construction, beside the allocation; to check at threading). The
    server reaches `storBnd` through raft's exported `memStorage_isStorage`, which gains the premise
    (Q6 item 8): its call `NodeStart.lean:322` discharges it from `srvClusterOk`. The harness uses
    `storBnd_zero : ⊢ storBnd γ K 0` (any `γ`).
  - `Advance`: **0** (F3, A5: `node.Advance.spec` keeps its text as the traced proof's instance).
  - Where the fact comes from: the server's `srvClusterOk` (`srvRaftLogInv`'s, read as
    `isRaftNodeIfc_of_isNode` does at `NodeBridge.lean:510`); kvreconf's and kvdurable's `isClusterC`
    `%Htr0` (their replica lemmas, `Replica__read`/`Replica__run`, take it from the cluster predicate if
    they hold it, else their replica predicate gains it: to check at threading); kv holds it only at
    allocation, so kv's `kvPeerOk` and its replica predicate (`isReplica`, for `KV__Read`,
    `KV__TransferLeadership`) gain it. In all, **about 25 call sites in 20 files**: the server 4 files
    (+ `NodeStart.lean`), kv 4 (+ `KVStorageInstance.lean`; + `Cluster.lean`'s and the replica's
    definitions), kvreconf 6 (+ `KvrStorageApi.lean`), kvdurable 6 (+ `KdStorageApi.lean`).
- L4 (revision 0's `threadBound ≤ 2^31`): closed by F1 (§6). **L5** (`TrNoSnap`'s source): closed by
  A4 (§5.2).

**The order of work (S5, S9; revision 2, B1): no `sorry` under an existing result, no new clause on a
proved theorem before its facts.** Each landing passes the acceptance test (`notes/trace-check-goal.md`).
1. **The gates and their client-side premises, one landing** (revision 1's steps 1 and 2 merged: the
   gated `netP`/`fwdP` break `ApiImpl.stepIn_intro_impl` and the local senders at a traced `γ` unless
   `stepIn_intro`'s premise and the refusals come with them). Each sealed definition changes as a gate
   whose `none` arm is today's body: `stepP` through `netP`/`fwdP`, `readyP` (the element and its
   allocation bound), `advInv`/`advDep`/`advRet`, `AdvReq`, `trTok`, `storBnd`; the escrow
   (`NodeNames`' `rtk`, `np`, `dep`, `al`; `rtkInv`, its slots `trTok`-bodied, in `isNodeChan`). With
   them: `stepIn_intro`'s `trTok` premise and the five refusals, `storBnd_zero` and
   `storBnd_intro_untraced`, and **every L3 call site** (about 25), each discharged; `trTok_type`,
   `trTok_untraced`; `isReadyChan_recvAu.tracedSpec` and **`node.Advance.tracedSpec` as the one proof,
   `node.Advance.spec` its instance** (both use only the driver's side of the escrow, so they are
   provable for every `γ` before `run`'s traced arms exist). Every proof of today's untraced results
   has `γ.raft.reTrace = none` (the premise of `node.run.spec`, `StartNode.spec`, `RestartNode.spec`,
   or the client's fact) and is re-proved by rewriting the gate. No `rnTrace` clause, no `readyTok` body
   change.
2. **The facts the new clauses need, as theorems** (no existing statement changes but the raft-internal
   ones named): L1's `OutTyStep` in `stepBundle_traced.statement`'s `Gout`, with the 27 path files
   re-proved (§3.6), and its physical half (`raft.send.spec`'s, `raft.sendTimeoutNow.spec`'s and
   `raft.Step.spec`'s traced premises, `XfOk`'s clause; untraced callers by `s.gh.tr = none`); G3 (a)'s
   gated clause on the term logs with the minting update's premise (`cluster_alloc_traced`
   establishing it); lemma (i) as a pure lemma over the committed log; `TrNoSnap`'s update form
   (`trNoSnap_traced`, the two `imod`s).
3. **`rnTrace`'s clauses 1(a)-(e) and `readyTok`'s `TrSent` body, one landing**, with every triple they
   re-open (§3.3: `RawNode.Tick.traced`, `acceptReady.spec`, `readyWithoutAccept.spec`,
   `wp_rn_raft_Step_prop_traced`, the assembly) re-proved in it from step 2's theorems. Nothing reaches
   a `sorry`; `etc/tcb-baseline.txt` does not move.
4. The traced arms as a theorem with the two ★ callees as **hypotheses**:
   `node.run.gated_of (hAdv : RawNode.Advance.tracedSpec) (hCC : raft.applyConfChange.tracedSpec) :
   node.run.gatedSpec` (no premise on the trace). Its hypotheses are complete (B1.5): L1, lemmas
   (i)-(ii), G3 and `TrNoSnap` are theorems by then, and each arm's other premises are §4's.
   Nothing existing depends on it.
5. Only when `hAdv` and `hCC` are proved is `node.run.spec` replaced: it becomes the gated statement
   (premise dropped), and today's statement survives as its instance (`node.run.spec_untraced`, if a
   caller still names it). The traced `newRaft`, `Bootstrap`, `setupNode` (with the minting, A8) and
   `StartNode.gatedSpec` are proved after.

**Amendment A8** lands on its own branch (`trace-check-a8`, done but `setupNode`'s minting): every
`simInit` reader under a closed result re-proved in that landing, none as a `sorry` (B1.4, §5.3).
It is independent of steps 1-5 above.

**Decisions taken in this pass (the agent's, recorded in `notes/decisions.md`, "Design pass (node
API, harness)", "Design pass, revision 1" and "Design pass, revision 2"):**
- the tokens at `node.Advance` through a claim on a per-node escrow (`rtkInv`, `np`), `run` needing
  nothing back (F3); revision 2: the allocation bound `al` for the driver-first order (A1, of the
  coordinator's two options), and `node.Advance.tracedSpec` the one proof with `node.Advance.spec` its
  instance (A5);
- one proved `node.Step.spec`, the gate in `stepIn`'s body, `stepIn_intro` taking `trTok` (F2);
- `TrSent` in the sealed `trTok`, and `trTok_type`; revision 2: the outbox's types as `OutTyStep` in
  `stepBundle_traced.statement`'s `Gout` (A2), with the physical half for the untyped messages;
- the five refused calls (`ProposeConfChange`'s premise used by its proof);
- the leader case of `confc` excluded rather than proved (lemmas (i), (ii) and G3, now a joint
  invariant: the term logs' gated clause and `rnTrace` 1(d), A3);
- `TrNoSnap` in its update form, built at `setupNode` from the client's storage contract (A4);
- `handleReady`'s conf arms from client-visible facts (`tc_confShaped`, `committed_emptyV2_joint`), as
  kvreconf (A6);
- A8's form as implemented on `trace-check-a8` (a mono list for the witnesses);
- Q33 by the existing `strconv.Itoa` axiom; the harness's `proto.Clone` by the existing `ClonePb` at
  `pbMessage`, the module moved to raft's tree (B4);
- Q34's local `netJoin` (under the instance) and `join3`; `app`'s thread token by `wp_fork_tok_body`
  (B5); Q35 (a);
- the harness's invariants `tcOpsInv` (with its requested-entries clause), `confPolicy`, `tcSnapsInv`;
- the order of work above.

**The user's:** §1 only, settled: Q32 (the premise bundle) and **Q38 (decided by the user, 2026-11-11):
`n + 2 ≤ 2^31` and `[ThreadBoundLe GF (2^31)]`, and the corollary's form**. No other change to a closed
statement or to the trust base is proposed: revision 2 adds no axiom (it uses the existing
`proto.UnmarshalConfChangeV2.wp_proof` and `ccDecodeV2_nil`, both already in raft's collection). The
tracecheck collection's baseline will gain the existing axioms of §6 when `RunConcurrent` is proved (a
collection update, not a trust-base change).
