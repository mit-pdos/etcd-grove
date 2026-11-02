# Stage F review: the server's and examples/kv's frozen statements (origin/repair ce2048af51)

Read-only review. Paths: `P/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`, `S/` = `Spec/go_etcd_io/etcd/server/v3/etcdserver/`,
`K/` = `Proof/github_com/mit_pdos/etcd_grove/examples/kv/`. Go: `.lake/go-src/etcd` (local checkout) and the pinned translation
`Code/go_etcd_io/etcd/server/v3/etcdserver.lean` (the fork's raft-loop and `applyAll` changes are confirmed there: the leader also
waits on `notifyc` in a conf batch, l.1016-1027; `close(raftAdvancedC)` after `Advance`, l.984-987; `applyAll` waits on
`raftAdvancedC`/`stopping` before compacting, l.2700-2709).

**Bottom line: four things block stage P's "prove each function once".** Without fixes, three tracks would have to change frozen
statements mid-proof, and one trusted axiom is unsound in the frozen state:
1. the `EtcdServer.snapshot` axiom is unsound against the frozen invariants;
2. the apply side's running-token half cannot be recovered for `raftNode.stop`;
3. `srvLogInv_alloc` lacks a premise its new invariant needs;
4. `srvDynLog` cannot be established from the frozen log invariant.

Everything else checks out or is minor. The D2 placeholders are noted only as dependencies.

---

## Tier 1: blocking (fix before stage P starts)

### T1a. The `EtcdServer.snapshot` axiom is unsound against the frozen invariants (D2-dependent, but unsound now)
- **Where.** `S/EtcdServer__snapshot.lean:54-72`, the axiom at `P/EtcdServer__snapshot.lean:25`. Changed in commit 37d6ddde33:
  - the post keeps `srvSnapState … sl` and claims nothing of the storage;
  - the pre drops `memCertReg`.
- **Evidence.**
  - Go `snapshot()` always calls `s.r.raftStorage.CreateSnapshot(ep.appliedi, ep.confState, nil)` (`server.go:2102`).
  - The memory trigger `appliedi > memorySnapshotIndex + 100` (`server.go:1225-1226`, `memorySnapshotCount = 100`, `:116`) fires
    under the frozen `NewServer` premise `receiptBound ≤ SnapshotCount` (`S/NewServer.lean:158,307,462`): any run past 100 applied
    entries reaches it.
  - After the real `CreateSnapshot`, the storage's lock invariant must hold again. Its stored-snapshot clause
    (`interface/Proof/go_etcd_io/raft/v3/InvMemstorage.txt:294`, `⌜index = 0⌝ ∨ J.SV sv ∗ J.DL …`) requires, at the server's
    `memStorJ` (`MemstorageApi.txt:9`), `snapshotValid` and so `snapMade`.
  - `srvClusterOk` holds `inv srvSnapsN (ownSnapsMade cl [])` for good (`P/SrvRaftLog.lean:685`), so `snapMade_elem` refutes it.
  - So no proof of the axiomatized triple exists in the server's world: the axiom is semantically false.
- **Consequence.**
  - The proof's refutations (`srv_sentMsg_notSnap`, `srv_readySnap_none`) assume no snapshot is ever made or sent.
  - In a real run, raft compacts after `compactRaftLog` and can then send a `MsgSnap` to a lagging follower: paths the proof calls
    `False`.
  - Callers: `snapshotIfNeededAndCompactRaftLog` (S-D), and through the link every server result whose run passes 100 entries.
- **Fix.** Make the axiom's pre carry what `CreateSnapshot` needs once D2 is answered (`J.SV` through a registry with an owner:
  D2(a)). Or, if D2 stays "no snapshot", make the snapshot unreachable by a premise, not by weakening the post:
  - e.g. `NewServer`'s run bound `receiptBound + |boot| ≤ memorySnapshotCount`;
  - or give the axiom a pure premise that its caller must discharge and cannot, e.g. `⌜uint.Z ai ≤ 100⌝`.

  Until then, `etc/tcb-report.py` should show this axiom as known-unsound, not as a trust boundary.

### T1b. The apply side's half of `nodeRunning` cannot get back to `raftNode.stop` (the running-token split)
- **Where.**
  - `isServerRun`'s `"Hrunh" ∷ rnRunHalf γn` (`P/InvRun.lean:410`; likewise `InvBuild:328`, `InvStart:231`, `StartOn:87`,
    `ServerOn:393`, `RunOn:91`);
  - `dvRun` lent to `applyAll`/`applyEntries`/`apply` (`P/InvCfgView.lean:368`; `S/EtcdServer__applyAll.lean:85,95`);
  - `run_job_body` (`P/EtcdServer__run.lean:54-80`: `dvRun` in the pre and post);
  - `raftNode.stop.spec` needs `rnRunHalf γ` (`S/raftNode__stop.lean:28-34`), which `rnStopBag` carries (`P/InvRaftNode.lean:854`).
- **Evidence.**
  - Jobs run asynchronously through the FIFO chain (`schedule.Scheduler.Schedule.spec`: a tracked job's `Post` goes only to the
    next job's `Prev`).
  - In Go, batch k+1 can be scheduled before job k returns: the raft loop's second `notifyc` send completes at job k's receive,
    `server.go:989`, before job k's `snapshotIfNeeded`/`raftAdvancedC` wait. So `run` cannot keep the half while a view job holds
    it; the half must travel in the chain.
  - But `schedule.Scheduler.Stop.spec` returns `True` (`Spec/go_etcd_io/etcd/pkg/v3/schedule/Scheduler__Stop.lean:30-37`). Once
    any batch with a view has run, the half is lost at `sched.Stop()`, and `run`'s deferred `s.r.stop()` (`server.go:825`) has no
    `rnRunHalf` to give.
  - A view batch always occurs: the boot `AddNode` entries are v1 conf entries, and `dvOk` forces `dv = some` for them.
- **Callers.** S-E's `EtcdServer.run.wp_proof(On)`. The frozen statements of S-C (`rnStopBag`, `raftNode.stop`/`onStop`) and S-D
  (`dvRun`) are shaped around this route.
- **Fix (either).**
  - (a) Strengthen `Scheduler.Stop.spec` to return `▷` the last tracked `Post` (the queue's last saved proposition). This is true
    of the Go: `fifo.Stop` waits on `donec`, which `fifo.run` closes only after executing every pending job
    (`pkg/schedule/schedule.go:150-184`). It reproves `fifo.Stop`/`fifo.run` only; mvcc's users never stop.
  - (b) Route the half with the view: `rnApGive`/`rnApR` (`P/InvRaftNode.lean:908-917`) carry `rnRunHalf` when `rnHands`, so it
    returns to the loop through `notifyc`, and `run` holds none. But the loop's `select {notifyc <- | <-stopped}` branch still
    needs a "jobs drained" witness from `r.stop()`, which again needs (a).

  (a) is the smaller change. Decide it now; both rewrite frozen statements.

### T1c. `srvLogInv_alloc` cannot establish the new `ccPolOk` conjunct
- **Where.** `srvLogCore` gained `∀ m ∈ Lf, m.typ = W32 1 → ccPolOk γ.raft m.data` (`P/SrvRaftLog.lean:~652`). The frozen
  `srvLogInv_alloc` (`P/SrvRaftLog.lean:2015-2027`) takes only `hidx`, `hnf`, `hnn` about `Lf0`: nothing about its conf entries'
  decodings. Counterexample: an `Lf0` with an `AddNode` of a non-member satisfies every hypothesis, and the conclusion's pure fact
  is false.
- **Caller.** `srvClusterBoot_alloc(On)`, which already has the needed fact as `hcc` (`P/NewServerAlloc.lean:176-177`).
- **Fix.** Add `(hcc : ∀ m ∈ Lf0, m.typ = W32 1 → ccBootOk (GMap.listToSet vs) m.data)` to `srvLogInv_alloc` (S-0's file).

### T1d. `srvDynLog` (in `srvApRes`) cannot be established from the frozen log invariant
- **Where.**
  - `srvDynLog` is now unconditional: `⌜lid ∈ cfg⌝ ∗ □ ∀ L, srvRLogLb γs L -∗ ⌜srvDynPol |boot| lid (pre ++ L)⌝`
    (`P/InvApRes.lean:238-240`). On lean it was `True` in the static mode the server used.
  - Its users: `srvApRes_cc` (`InvApRes.lean:390-420`, exporting `srvDynPol`) and `dvView_cc`'s `Hdyn` (`InvCfgView.lean:428-441`).
- **Evidence.** `srvDynPol` says every committed `AddNode` sits at a position below `|boot|`. `srvRLogLb` (`SrvRaftLog.lean:389`)
  knows only committedness and `srvIdxOkW`, and `srvLogCore` records no position fact for type-1 entries. So the persistent
  `□ ∀ L` that `NewServer`/`start` must build at the start (S-E) is unprovable. It is true in Go (the server proposes no conf
  change), but the invariant does not say so.
- **Fix (either).**
  - (a) Add `∀ j m, Lf[j]? = some m → m.typ = W32 1 → j < γ.raft.boot.length` to `srvLogCore`. Proposals append type 0, and the
    allocation's `Lf0` is the boot log. This is S-0's.
  - (b) Under D3, return `srvDynLog` to its static form `⌜lid ∈ γs.raft.cfg⌝`, and drop `srvDynPol` from `srvApRes_cc`'s post and
    `dvView_cc`'s `Hdyn`. With only `AddNode`s of voters (`ccApplyOk`), the positions are irrelevant: `srvPeersCover` with
    `nodeId ∈ cfg` gives `nodeId ∈ prs`.

  (b) is simpler and matches D3.

---

## Tier 2: D2 dependencies (PENDING placeholders; not reviewed beyond this)

D2(i) as frozen is false of the Go (T1a's trace, and `ForceSnapshot` at `apply/backend.go:283` on a downgrade). The answer moves
these shared statements, so the tracks that use them would change mid-proof:
- `srvClusterOk`'s `inv srvSnapsN (ownSnapsMade cl [])` (`P/SrvRaftLog.lean:685`). Under D2(a) it becomes the design's `∃ S` with
  records, and every refutation changes: `srv_snapMade_false`/`_snapshotCert_false`/`_snapshotValid_false`/`srv_sentMsg_notSnap`/
  `srv_readySnap_none` (`:1540-1582`), and their users `rnMsgOk_of_api` (`InvRaftNode.lean:~430`), `rn_ready_recv`, `InvNet`, and
  `rnSnapOnce`.
- The trusted `node_contract_memstor` through `rnAppendReceipt γ es := appendReceipt st es []` (`InvRaftNode.lean:~196`). The
  notes say to revisit it if D2 registers snapshots: then `CreateSnapshot`'s `memLog i □ [e]` needs the frozen prefix `a`.
- The trusted `NewServer.spec`/`specCompact`/`specM` run bound (three copies, `S/NewServer.lean:158,307,462`). The design's
  "one shared premise bundle" (§5 Stage F) was not done, so D2's answer is again three edits.
- `srvSnapState`, `compactRaftLog.spec`, `snapshotIfNeededAndCompactRaftLog.spec`, `ModeSpecs`, `SnapTake*`.
- **Recommendation.** Answer D2 before starting S-0 and S-C, which own the refutations; those two tracks are the user's
  first-priority ones. If D2 = "unreachable", the cheapest sound form is the run bound below `memorySnapshotCount` (with
  `ForceSnapshot` excluded by `rqShape`); the registry and the refutations then stay as frozen.

---

## Tier 3: minor (log and continue)

- `bootOk` (in the trusted `bootstrapContract`, `P/InvBoot.lean:247`) and the new section instance arguments in the server's
  `Results.lean` (`[raftAsm]`, and `[srv_sem]` for `server_applied_predeposit_on`'s section, `Results.lean:2374,2420-2423`) are
  logged in the plan but not in D5's §2c list. They are benign, but show them to the user with the D5 diff.
- `kvJ` (`K/KvStorage.lean:433`) duplicates raft's `memStorJ` field for field, and appears in the trusted `kv_storage_isStorage`
  and `kv_bootStorage`. Consider stating them with raft's `memStorInv` (if the `MemStorReg` instance allows), so the trusted text
  uses raft's vocabulary.
- `rnRunHalf`/`dvRun` are new client-visible ghost state (in the exported `NodeStartSpec`'s post), a logged deviation the
  coordinator agreed to. The standing rule escalates it to the user; it falls under T1b anyway.

---

## Per question

### (1) Provable from raft's API and callees?
False or unprovable as frozen: T1a (axiom), T1c (`srvLogInv_alloc`). Unprovable without a statement change: T1b (`run`), T1d
(`srvDynLog`). Checked and provable:
- `srv_confAt_simple` and `srv_committed_noV2`: see (5).
- `srvRule_keeps` (`InvCfgView.lean:86`): `ccRaftEff` keeps `AddNode v` (v a voter) or zeroes `NodeId`; `applyChange_addVoter`/
  `_nodeZero`; non-type-1 entries give `none`.
- `raftApplyCC_of_isNode`:
  - `confPolicy_decide` at `srvConfN`, with `deliveredLogLb_committed`;
  - `confAt` from `nodeConfig_confAt` (R3) plus `confAt_noConf` over `srvCCPre`'s `NoConfChangeIn`;
  - `skippedIn_noConf`; the stopped answer refuted by the lent `nodeRunning q`.
- `isRaftNodeIfc`'s clauses against `node.Advance`/`Tick`/`Stop`/`ReadIndex`:
  - Advance's `advReceipt` with `a = []` and `L = none` (under D2(i));
  - `nodeAppliedLb |delivered|` with `pre = []`;
  - Tick/Stop as raft's specs.
- `srvMem_bootStorage` (`NodeStart.lean:229`): same shape as the proved `kv_bootStorage`; `MemoryStorage.InitialState` gives back
  `memStorFresh`, then `memStorInv_alloc` runs inside the continuation.
- `compactRaftLog.spec` against `Compact` (mono laws). Unreachable under D2(i): Tier 2.
- `readyFits` from `readyFits_intro` with `Hrb2` (`NewServerAlloc.lean:174`).

### (2) Invariant facts each function needs
- **`raftNode.start` / `rn_ready_recv` (S-C).**
  - Needs: `srvClusterOk` (`readyFits`, the refutations: Tier 2), `srv_committed_noV2` (mask `srvConfN`, outside `srvRaftN`: fine),
    `rnCfgAt`, `rnRunHalf` (in `rnLoopTokP`, `InvRaftNode.lean:997-1002`), `nodeAppliedLb` for `raftAdvancedC`.
  - Sufficient, except Tier 2.
- **`applyAll` / `apply` / `applyConfChange` (S-D).**
  - Needs: `dvView`/`dvRes`/`dvRun`; `srvApRes` with `srvDynLog`, gap T1d; `srvIdxOkW`'s type 0/1 (`KVModelDefs.lean:160-163`),
    kept by `srv_committed_noV2`.
  - Sufficient after T1d.
- **`NewServer` / `start` / `run` (S-E).**
  - Needs: `srvLogInv_alloc` (T1c), `srvDynLog` (T1d), the half's return (T1b).
- **`srvLogCore`'s new conjuncts.**
  - `¬isEmptyV2`: preserved by proposals (normal entries).
  - `ccPolOk`: preserved by proposals (type 0) and established at allocation only with T1c's premise.
- **kv `run` (K-b).**
  - The pre (`nodeConfig ⟨0, kvMembership⟩`, `nodeRunning 1`, `kvCluster`, `runStor`) suffices:
    - `CreateSnapshot`'s `J.SV` from `kvSnapInv` (`snapshotCert_make`/`_valid`), and its `J.DL` from `deliveredLogLb`;
    - `Compact`'s `J.B` from Advance's `nodeAppliedLb`, and its `memSnapLb` from `CreateSnapshot`'s post;
    - empty V2s refuted by `committed_emptyV2_joint` at `confAt k kvMembership`, built inductively as for the server
      (`NormalReqs` rules out v1 entries).
  - No gap found.

### (3) Trusted statement changes vs origin/lean
- **kv.** `kv_porcupine_safe` is byte-identical (`K/Results.lean:201-213`; no diff hunk). The Go change is only `RemoveMember`'s
  removal (`examples/kv/kv.go`, and the test). The other kv changes are all within D4/D5: `kv_RemoveMember` deleted,
  `kv_storage_isStorage` (the new premise `memStorInvP … (kvJ γ id)`), `kv_bootStorage` replacing `kv_storage_initialState`, and
  `kv_Read`/`kv_New`/`kv_run`/`kv_NewStorage`/`kvStorInv_alloc` through their specs.
- **Server.**
  - `node_contract_ifc` loses `rnStopOk`.
  - `server_cluster_alloc_on`: `γ.rule = srvRule 0 boot` in place of `dyn = false`; no `readCredits`.
  - Callee lists of `node_contract_propose`, `server_raft_node_start`, `server_new_auth_on`.
  - Section instance arguments (Tier 3).
  - Under the definitions: `isRaftNodeIfc`, `NodeStartSpec` (+ `rnRunHalf`), `bootOk`, `NewServer.spec*` (the D2 premise),
    `isRNMemStor`.
  - All within D5 except the instance arguments and `bootOk`, which are not in the §2c list, and the PENDING D2 premise.

### (4) New client-visible ghost state not in the design
- `rnRunHalf`/`dvRun` (T1b, Tier 3).
- `SrvRaft.rule` and the pure `srvRuleKeeps` in `srvClusterOk`.
- The namespaces `srvConfN`, `srvSnapsN`.
- The registry invariant in its D2(i) form (`[]` in place of the design's `∃ S`).
- kv: `kvJ` (a duplicate).
- Nothing else.

### (5) The `nodeRunning` split, and refuting empty `ConfChangeV2`s
- **The split is necessary and sound in principle.**
  - The apply thread's `node.ApplyConfChange` (`server.go` `applyConfChange`, which dereferences the returned `*ConfState`) races
    the loop's `Advance` only in non-conf batches.
  - `node.Stop` runs only in `onStop`, after `r.stop()`, which `run` calls after `sched.Stop()` drains the jobs.
  - But the frozen route cannot close: T1b.
- **Empty `ConfChangeV2`s: refuted correctly.** `srv_confAt_simple` (`SrvRaftLog.lean:814`) is provable by induction on `k`:
  - a non-conf entry: `confAt_noConf`;
  - a v1 entry: by `srv_entry_src` it is a server-log entry, so `ccPolOk` holds, so `ccBootOk cfg`, and `srvRuleKeeps` clause 1
    gives `step = some (simple cfg)`; then `confPolicy_decide` and `confAt_decided`;
  - an empty V2: rule `none`, so `skip`, or directly `committed_emptyV2_joint` against `simple`'s empty `votersOutgoing`.

  `srv_committed_noV2` (`:824`) follows. Both need only `srvConfN` and `srvLogN` in the mask, and are sound. Non-empty V2s cannot
  be committed: they would be in `opsOf`, so in the server's log, whose entries `srvIdxOkW` restricts to types 0 and 1. That
  closes etcd's `apply` panic on type 2 (`server.go` `apply`'s `default:` branch).

### (6) The sorry list
- The file-level coverage matches the plan's "Stage F sorries" exactly: every file that gained a `sorry` versus origin/lean is
  listed.
- No `sorry` makes a target vacuous under D2(i): the refutation lemmas are provable from `snapMade_elem`.
- The only vacuity risk is T1a: the unsound axiom, not a `sorry`.

---

## What is good
- The empty-V2 handling: `opsOf_nofill`, `srv_entry_src`'s third alternative, `srv_committed_noV2`, with `srvConfN` outside
  `srvRaftN`.
- `srvRuleKeeps` as a pure, rule-level statement of D3.
- `raftApplyCC` lends `nodeRunning q` and takes `srvCCPre` at the cluster's rule. It is the right contract for
  `node.ApplyConfChange`.
- The `Advance` clause's `nodeAppliedLb` in place of the storage floor, matching raft's API and `Compact`'s `J.B`.
- The strengthened `MemoryStorage.Snapshot.spec`, which `run`'s `lg.Panic` on error needs.
- kv:
  - `kvCluster_alloc` is clean;
  - `kv_porcupine_safe` is untouched;
  - the D4 removal is complete (Go, test, translation, spec, proof, link);
  - `kv_bootStorage` is proved.

## Targets ranked by need of revision
1. `S/EtcdServer__snapshot.lean` (the axiom) with the D2 bundle (`srvClusterOk`'s registry, `NewServer`'s run bound ×3): T1a,
   Tier 2.
2. The running-token route: `isServerRun`/`isServerBuilt`…`"Hrunh"`, `dvRun`, `run_job_body`, `rnStopBag`, `raftNode.stop.spec`,
   and `schedule.Scheduler.Stop.spec`: T1b.
3. `P/InvApRes.lean` `srvDynLog`, plus `srvApRes_cc`/`dvView_cc`'s `srvDynPol`, or `srvLogCore`'s position fact: T1d.
4. `P/SrvRaftLog.lean` `srvLogInv_alloc`: T1c (a one-line premise).
5. Trusted-text hygiene: `bootOk` and the instance arguments in the D5 diff; `kvJ`; the shared `NewServer` premise bundle
   (Tier 3).
6. kv's statements: no revision needed.

No Go bug found; nothing new for `issues/`. The memory-snapshot trigger contradicting D2(i) is a spec-scope fact, already in the
plan's findings.
