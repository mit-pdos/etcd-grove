# Repairing etcd's server and examples/kv against raft's new API: design study

2026-10-30. A read-only study. Raft's API is `repair`'s (68a3b730c6 = raft-final + kvreconf-final). The client
trees are **origin/lean's** (08b447f059), extracted to `/home/ubuntu/.claude-E/jobs/c8379647/tmp/lean-tree/`, because
lean is merged into `repair` before the repair starts. At the time of writing that merge is in progress, unresolved, in
the worktree. Line numbers of server and kv files are lean's.

Abbreviations: `P/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`; `S/` = `Spec/go_etcd_io/etcd/server/v3/etcdserver/`;
`K/` = `Proof/github_com/mit_pdos/etcd_grove/examples/kv/`; `R/` = `Proof/github_com/mit_pdos/etcd_grove/examples/kvreconf/`;
`I/` = `interface/Proof/go_etcd_io/raft/v3/`; `IS/` = `interface/Spec/go_etcd_io/raft/v3/`.

The study had three parts: (1) the server's node, net and allocation side, (2) the server's storage, snapshot and
compaction side, (3) kv. The user's design input on MemoryStorage arrived mid-study and is built in: the shared
`memSnapLb` replaces `memSnapExact`.

---

## 0. Decisions needed before any proof work (summary)

| # | Question | Options | Recommendation |
|---|---|---|---|
| D1 | **StartNode.** The server's new-cluster path calls `raft.StartNode(cfg, peers)` (etcd `server/etcdserver/bootstrap.go:578-584`). Raft has no StartNode spec, and `cluster_alloc` allocates an empty-log cluster only (`I/InvNodeRule.txt`, `cluster_alloc`). | (a) Raft work: a decision-cluster allocation with a bootstrap log, plus a unified `StartNode.spec`. Go unchanged. (b) Fork Go change: a new cluster starts by `RestartNode` over a wrapper Storage that answers the peers' ConfState. (c) A trust-boundary axiom for StartNode. | **(a).** (b) is not just one wrapper. It needs at least two more fork changes, because etcd relies on the boot AddNode entries: they write the members to the backend (`server.go:2026-2042`, `membership/cluster.go:394-405`), so without them `ValidateConfigurationChange` rejects later RemoveNodes (`cluster.go:357-360`). They are also the only thing that sets `ep.confState` from the empty boot snapshot (`server.go:802-811`); without them every `CreateSnapshot` carries an empty ConfState, which `snapshotValid` refutes, and Go would send a wrong MsgSnap. (a) costs about 1-2k raft lines (`raft-gap-design.md`'s P8 estimate: 1000-1500; the old StartNode proof was 451 lines and setupNode 66; `RawNode.Bootstrap` is kept, 597 lines). |
| D2 | **MsgSnap.** Raft may now send and hand out snapshots in every cluster; the no-snapshot mode is gone (`notes/raft-unified-plan.md`, U8 v2 step 3a). The server's proof today makes every snapshot path `False`. | (a) Verify the snapshot path: sender (merge plus `sentMsg_replaceSnapshot`) and receiver (`applySnapshot.specSnap`, already proved). (b) A client cap witness `storCompactCap`, which means re-adding the no-snapshot mode to raft. (c) A trust-boundary spec for the merged message. (d) A Go change. | **(a).** It also removes the trusted run-length premise `receiptBound ≤ SnapshotCatchUpEntries` (`S/NewServer.lean:155,303`), under which the old result covered only runs shorter than 5000 entries and never really compacted (`P/InvApplyAll.lean:105-108`, `cap = 1`). (b) reverses U8 v2's recorded direction (the user's "follow recorded direction"). Raft work for (a): see R4. |
| D3 | **RemoveNode / membership changes after boot.** Under the new `ApplyConfChange` they are reachable in principle. Then `EtcdServer.IsIDRemoved`'s spec `RET #false` (`S/EtcdServer__IsIDRemoved.lean:33`) and `netRaftOk` (`api/rafthttp/Net.lean:197-198`) are false, and `Process`'s 403 and the stream handler's 410 become reachable. | Keep membership static: the KV policy admits no post-boot conf change, so every `confAt` is the boot membership. Or widen these specs. | **Keep static** for this repair (the scope today). Record it as a scope note. |
| D4 | **kv's `RemoveMember`.** | (a) Keep its premise ("the removed id is not a voter"), redefined without `CCShrink`; no Go change. (b) A Go change: guard `ApplyConfChange` with `validConf` as kvreconf does, and drop the premise. | **(a)** for this repair, since `kv_porcupine_safe` does not reach `RemoveMember`. (b) would follow kvreconf and fix the inherited `issues/raft-remove-last-voter-panic.md`; schedule it later. |
| D5 | **Trusted-statement changes** (sections 2 and 3). | — | Approve the list. They are mostly deletions of premises: `readCredits`, `leaderTransferOff`, `γ.dyn`, `rnStopOkStarted`, the run-length premise. |

The standing rule says new client-visible ghost state is escalated. The repair would add the following; none of it is
built yet:
- the server's snapshot-registry invariant (`inv srvSnapsN (∃ S, ownSnapsMade γ S)`): server-internal, built over raft's existing `ownSnapsMade`;
- in raft (R1, R4): `memSnapLb`, and a "stored-snapshot witness" on `sentMsg`.

---

## 1. Raft's API delta as the clients see it

The exact text is `git diff origin/lean repair -- interface/Spec/go_etcd_io/raft interface/Proof/go_etcd_io/raft`.
`/home/ubuntu/.claude-E/jobs/c8379647/tmp/repair-api-delta.md` has the full list. The client-relevant points:

**Clusters and allocation.**
- `isStaticCluster`, `isDynamicCluster` and their allocations are gone: one `isCluster γ N`.
- `cluster_alloc N vs dup` (`I/InvNodeRule.txt`) takes `receiptBound ≤ 2^64-2`, `vs ≠ []`, `Nodup`, `0 ∉ vs`, `|vs| < 2^62`, and gives:
  `⌜γ.dup = dup⌝ ∗ ownCommittedOps γ [] ∗ ownReadCtxs γ ∅ ∗ isCluster ∗ ownConfDecisions γ ∅ ∗ confAt γ 0 (simple vs) ∗ ownSnapsMade γ [] ∗ joinAuth γ vs ∗ [∗] nodeFounder γ N vs id`.
- It is empty-log only: no `BootLog`, `bootMarshal`, `ctxs`, or `readyFits`.
- **API gap:** `readyFits`/`Cluster.bootLen` have no introduction law, and the server needs `readyFits` for `MemoryStorage.Append`'s `k + |es| ≤ 2^61` through `readyRest_fits`. That is raft work R2.

**Starting a node.**
- `StartNode.spec` and `StartNode.dynamicSpec` are **deleted**; there is no StartNode spec at all (A5 of the gap design deferred it "to U10").
- The only start is `RestartNode.spec` (`IS/RestartNode.txt`):
  - premises: as before on `cv`, `HsEmpty hs`, `csm` the voters `vs` (no outgoing voters, no learners, no autoLeave);
  - pre: `bootStorage γ id st hs csm Q ∗ (nodeFounder ∨ nodeJoin ∗ confAt γ 0 (simple vs) ∗ ⌜vs.Nodup⌝)`;
  - post: `isNode ∗ nodeDriver (init st) ∗ nodeConfig {0, simple vs} ∗ nodeRunning n γ N 1 ∗ Q`.
- `bootStorage` (`I/InvNodeRule.txt`) is a frame `R` with:
  - triples `FirstIndex = 1` and `LastIndex = 0`;
  - an `InitialState` answering `(hs, csm)`, with an update to `isStorage γ id st ∗ storLog st 0 □ [e0] ∗ storEnd st 1 ∗ Q`.

  A **bare MemoryStorage cannot give it**: its `InitialState` answers the empty ConfState. A wrapper can (kvreconf's `R/KvrStorageApi.lean`, `kvr_bootStorage`).

**Storage.**
- The `StorageModel` class is `storLog`/`storEnd`/`storCompacted` (range ownership).
- `isStorage γ id st := isStorageP (snapshotValid γ) (storBnd γ id) (storDL γ id) st`.
- `snapshotValid` is exposed: a committed prefix, `confAt`, `snapMade`, and `0 < index < 2^61`, plus the lists' bound.
- `snapshotCert_make`/`_made`/`_valid` work over the client-owned `ownSnapsMade`.
- `MemstorageApi`: `memStorJ γ id`, `memStorInv` (`memStorInv_alloc` from `memStorLock ∗ memStorFresh`), `memStorage_isStorage`.
- MemoryStorage's specs (`IS/MemoryStorage__*.txt`): `CreateSnapshot` needs `J.DL i = storDL` (a `deliveredLogLb` of length `≥ i`) and `J.SV`; `Compact` needs `J.B x = nodeAppliedLb ∨ snapGiven`; `ApplySnapshot` needs `J.B`/`J.SV`/`J.DL` and `s < 2^61`.
- Today `memSnapExact` (exclusive) is needed by `ApplySnapshot`, `CreateSnapshot` and `Compact`. **By the user's design input it is to be replaced by the persistent `memSnapLb` (R1, not built).**
- `InitialState` needs `memStorMeta ∗ memStorFresh` (before the invariant). `SetHardState` is importable.
- Gone: `StorState`, `ownStorage`, `storFloor`/`storCap`/`storCert`/`storTermsAt` as client vocabulary, `memSnapTok`, `memCertAuth`, `memStorCert`, `storageCertInv`/`storageCertLink`, `MemstorageAU`, `MemCertLink`, `snapshotCert_static`/`_data`.

**`Ready` / `Advance`.**
- `readyRest`/`readySnap γ N id …` now take `id`.
  - `none`: `appendRight ∗ ceFrozen ∗` an indices fact (`readyRest_indices`, `readyRest_ceInBatch`).
  - `some l`: `snapshotCert`, ranges from `k ≤ s` with the end, and `snapGiven γ id s`.
- `advReceipt st |delivered| es L` (`appendReceipt st es a` with a frozen prefix `a`), `snapReceipt`.
- `node.Advance.spec` (`IS/node__Advance.txt`):
  - pre: `isCluster ∗ isNode ∗ nodeDriver ∗ advReceipt ∗ nodeConfig v ∗ (L = none → skippedIn | some l → snapshotCert)`;
  - post: `nodeAppliedLb γ id |delivered|`, plus `nodeConfig` (at the snapshot, with `confAt` and `confStateIs`), or `nodeStopped`.
  - The old `memFloorAtLeast`/`storFloor` post is gone.

**Conf changes.**
- `node.ApplyConfChange.spec` takes `confDecided γ k (apply o') ∗ skippedIn ∗ deliveredLogLb ∗ nodeConfig`; its post is the change, or `⌜csp = null⌝ ∗ nodeStopped`.
- Decisions go through `ownConfDecisions`/`confDecide`, or the persistent `confPolicy`/`confPolicy_alloc`/`confPolicy_decide` (`I/ConfPolicy.txt`).
- `CCShrink`/`ccShrink_addVoter` are gone.
- There is no law `nodeConfig ⊢ confAt` (Q6 of the gap design, deferred). That is R3, optional.

**Proposals and errors.**
- `Propose`/`ProposeConfChange` take their update under `□?γ.dup`. Server and kv allocate `dup = false`, so it is a plain AU.
- `ProposeConfChange` commits `ops ++ opsOf [entry]`.
- Posts: `propErrS`/`nodeErrS` (K5: a stopped answer carries `nodeStopped`). `nodeErrS_nodeErr` and `propErrS_propErr` convert back.

**Credits and modes.**
- `readCredit(s)`, `tickCredit` and `leaderTransferOn/Off` are gone.
- `Tick`, `ReadIndex` and `TransferLeadership` take only `isNode` (and the context).
- New specs: `Stop` (`nodeRunning 1` → `nodeStopped`), `Status`, `Campaign`, `ForgetLeader`; `nodeRunning_stopped`.

**Messages.**
- `NetMsgOk` is internal, and `NetMsgOk.of_sent`/`netStepTypes`/`UnstampedType` are gone.
- `stepIn_intro` is `To = id → sentMsg ∗ msgPtsC ∗ msgCredits ⊢ |==> stepIn`: no transfer, MsgSnap, pre-vote, booted or tick premise.
- `sentMsg_shape` replaces `sentMsg_transferOff`/`sentMsg_dynamic_notSnapshot`.
- `msgCredits_intro` (for non-`MsgProp`), `msgCredits_copy` (for `dup`). `msgCredits_none`/`_snapshot` are gone. `sentMsg_replaceSnapshot` is kept.

---

## 2. Gap table: etcd's server (lean's tree)

### 2a. Node, network and allocation side

| Cause | Files (size) | Kind |
|---|---|---|
| **StartNode gone; `nodeBoot`/`nodeDynamicBoot` gone; `cluster_alloc` reshaped** | `NodeStart` (471; `NodeStartSpec` :245-340, the storageCert/storCap rows, the InitialState closure); `bootstrappedRaft__newRaftNode` (Proof 223, Spec 145); `NewServerAlloc` (355; `srvClusterBoot_alloc` :169); `NewServerAllocOn` (250); `BuildAlloc` (323: `kvInv_alloc_boot`, `bootEntries_ok`) | Reproof |
| (same) | `S/NewServer` (582; three statements: `spec` :125, `specCompact` :274, `specM on` :427, each with `γ.dyn = false` :137/286/439, `nodeBoot` :183/331/489, `readCredits` :191/339/497, `rnStopOkStarted` :228/376/534); `P/NewServer` (2018); `InvNodeStart` (197) | Restatement, plus a reproof of the allocation and start points |
| (same) | `NodeApiLink` (94: drop `StartNode`/`_dyn`, `Advance_dyn`, `ApplyConfChange_dyn`; add `RestartNode`, `Stop`; under D1(a), the new `StartNode`); `Link.lean` and `etc/link-lean-first-server.txt:547` | Regenerate |
| **One mode** (`isStaticCluster`/`γ.dyn` gone: every boot batch now hands the configuration view to the apply thread) | `InvCfgView` (442: `srvDec`, `srvDynCCPre`, `raftApplyCCDyn` :268, `srvRaftNodeDyn` :295); `EtcdServer__applyConfChange` (Proof 939, Spec 106); `InvRaftLoop` (214) | Reproof |
| (same) | `EtcdServer__run` (1429; its `dyn`/`dec` clauses); `NodeBridge` (620: `raftApplyCCDyn_of_isNode` :372, `isRaftNodeIfc_of_isNode` :410); `InvRaftNode` (1066: `rnHands` :892, the `rnEnvOk` dec clause :269) | Medium |
| (same) | `ServerOn`, `InvApRes`, `EtcdServer__apply`, `InvRun`, `InvStart`, `StartOn`, `RunOn` (one or two `.dyn` premises each) | Light |
| **Read credits gone** | `SrvRaftLog` (`srvRdCred` :584, `srvRdFreshInv` :1640/1675/1777); `NewServerAlloc` `readCredits_members` :130; `InvRaftNode` `rnReadCred` :247; `raftNode__ReadIndex` (47); `read/Inv.lean` :252/266/324 | Light. Delete the credit outright, which also simplifies the read package's `requestCurrentIndex`/`sendReadIndex` specs. |
| **Transfer, no-snapshot and credit premises gone** (`leaderTransferOff`, `sentMsg_transferOff`, `msgCredits_none`, `NetMsgOk`, `bootedCluster`, `tickCredit`) | `InvNet.stepIn_of_recv` (108; becomes `stepIn_intro`); `InvBuild.srvNet` (399; :136-141, `dup` becomes `msgCredits_intro`); `srvMsgNet_bundle` :163; `BuildGap` :167; `tickCredit_zero` in `InvNet`; `isRaftNodeIfc`'s Tick `{{⧗ 1}}` → `{{True}}` | Light |
| **`nodeErr` → `nodeErrS`, `propErr` → `propErrS`** | `NodeBridge` (`rnStepIfc`, `applyErrIs_of_*`), `ProposeOn` (812), `EtcdServer__processInternalRaftRequestOnce` | Light (the `_nodeErr` laws) |
| **Propose under `□?γ.dup`** | `SrvRaftLog` :1025, :1276 | Trivial (`γ.dup = false`) |
| **`node.Advance`'s new spec** | `isRaftNodeIfc`'s Advance clause (`InvRaftNode` :379-405), `raftNode__start` (862), `rnCfgAt` | Medium (the old dyn branch is the template) |
| **`readySnap`/`readyRest` take `id`; new conjuncts** | `rn_ready_recv` (`InvRaftNode` :542-690) | Medium |
| **`nodeRunning`/`nodeStopped`** | `rnStopOk`/`rnStopOkStarted` (`NodeBridge` :54/:110) become provable by `node.Stop.spec` | Light; removes a trusted premise from `NewServer` |

### 2b. Storage, snapshot and compaction side

| Cause | Files (size) | Kind |
|---|---|---|
| **A. The no-snapshot mode is gone**: `srvClusterOk` (`SrvRaftLog` :644-660) and the refutations `srv_sentMsg_notSnap` :1458 and `srv_readySnap_none` :1482 | Users: `InvNet:81`, `BuildGap:198`, `ServerOn:697`, `InvRaftNode:443,579`, `NodeBridge:469` | The lemmas (~50 lines) are deleted; each user is reproved |
| **B. Snapshot paths stubbed to `False`** | `InvRaftNode`: `rnSnapMsg` 168, `rnMsgR` 175, `rnReadyData`'s `Snapshot = null` 207-219, `rnReadySnap`/`rnBusyS` 694-703, `rnApSnap` 937, `rnApP` 942. `raftNode__start` (862; the snapshot branch, raft.go:256-282, is unproved). `raftNode__processMessages` (402; the `msgSnapC` arm, :213-218). `EtcdServer__applyAll` (436; `Hnosnap`). `NewServer:1493` | Reproof: `raftNode.start` +~400, `applyAll` +~250, `processMessages` +~60. `applySnapshot.specSnap`/`wp_proof_snap` and `SnapApply*` (~2.5k lines, already proved, mostly raft-independent) need only their premises rewired. |
| **C. Old MemoryStorage vocabulary** (`MemstorageAU`, `memSnapTok(G)`, `memSnapRO`, `memKey γs.ak`, `memTokShared`, `memFloorTok`/`memFloorAtLeast`, `γs.cap`, `memCertAuth`/`memCertReg`/`memStorCert`, `ownStorage`/`memStorEmpty`, `StorState`) | `InvApplyAll` (239: `srvSnapState`, `srvStorTok_alloc`, the shared-token workaround :123-166); `SnapTake` (225); `SnapTakeProof` (382); `EtcdServer__snapshot`; `EtcdServer__compactRaftLog` (164); `EtcdServer__snapshotIfNeededAndCompactRaftLog` (116) and its specs in `ModeSpecs:50-90`; `InvRaftNode:366-371,862,920`; `EtcdServer__run:69-1339` (its `Snapshot()` and the token allocation :438-450, :958-970); `InvRun:270,310`; `InvBoot:263-299`; `InvRaftLoop:61,68`; `InvBuild:209-212`; `newRaftNode` | ~1.5k lines touched. `compactRaftLog` and `snapshotIfNeeded` are light (same shape). The `SnapTake*` CreateSnapshot call is a reproof. |
| **D. Append and receipt API** (`appendReceipt … a`, `advReceipt`/`snapReceipt`, `ceFrozen`) | `InvRaftNode:184-193` (`rnAppendRight`/`rnAppendReceipt`), `isRNMemStor` 707-716; `raftNode__start:525`; `Results:278-283` `node_contract_memstor` | Light, but the trusted `node_contract_memstor` changes |
| **E. The MsgSnap sender and receiver** (`InvSnapSend` 105, `SnapSendBranch` 279, `SnapRecvFacts` 451, `createMergedSnapshotMessage` 164, `sendMergedSnap` 261, rafthttp `snapshotSender__send` 337, `snapshotHandler__ServeHTTP` 565, `Net.lean` `netSnapBundle`/`snapDirInv`) | ~2.1k lines exist, proved over D22, then made dead | Under D2(a): light fixes of the bodies; the raft-facing premises are reproved (`sentMsg_replaceSnapshot`, `rnSnapMsg`). |

Where lean's server differs from repair's copy:
- `NewServer` has three statements, not one, so every premise change is made three times. Factor one shared premise bundle first.
- `ModeSpecs` restates `snapshotIfNeededAndCompactRaftLog.spec`/`specOn` with the old storage premises.
- `CompactEnv`/`CompactMode` are MVCC compaction, outside this repair.
- `EtcdServer__snapshotIfNeededAndCompactRaftLog`'s proof was restructured (−83 lines; its specs moved to `ModeSpecs`).
- Lean already works around the shared snapshot token with an invariant and a client counter `γss` (`P/InvApplyAll.lean:123-166`). That counter is what `memSnapLb` (R1) will provide from raft.
- The pinned fork has three Go facts the local checkout lacks: `close(raftAdvancedC)` after every `Advance` (translation l.927), `applyAll` waiting on `raftAdvancedC`/`stopping` before compacting (translation l.2546; `issues/etcd-compact-past-raft-applied.md`), and the merged MsgSnap sent only at `m.Term == raftTerm` (D22a).

### 2c. The server's exported, trusted results (`P/Results.lean`) that must change

| Result | Old | New |
|---|---|---|
| `server_raft_node_start : NodeStartSpec` (:295) | `StartNode`, `nodeBoot`, `storageCertLink`/`storCap`, the InitialState closure with `memSnapTok`, `rnStopOkStarted` | Under D1(a): the same shape over raft's new `StartNode.spec` (the boot allocation's per-node token, `isStorage`/`memStorInv`). The post gains `nodeRunning 1`, and `rnStopOkStarted` goes. Under D1(b): over `RestartNode` + `bootStorage` + `nodeFounder`. |
| `server_cluster_alloc_on` (:2151) | `BootLog`/`bootMarshal`/`ccBootOk` premises, `γ.dyn = false`, per member `readCredits (2^48) ∗ nodeBoot` | No `dyn`, no credits. Per member, the new boot token (D1(a)) or `nodeFounder` (D1(b)). `srvClusterOk` holds `isCluster ∗ confPolicy (srvRule …) ∗ readyFits ∗ ⌜dup = false⌝` and the snapshot registry. BootLog/bootMarshal only under D1(a). |
| `server_member_alloc_on` (:2178) | — | Unchanged unless `ReqNames` changes |
| `server_new_auth_on : NewServer.specM true` (:2096), and `NewServer.spec`/`specCompact` with their composites | `γ.dyn = false`, `Hnboot`, `HrdCred`, `#Hstop`, `receiptBound ≤ SnapshotCatchUpEntries` (:155/303/453), `memStorRegAuth ∅` | Drop `dyn`, `HrdCred`, `#Hstop` and, under D2(a), the run-length premise. Add the boot token. Keep `memStorRegAuth ∅`. |
| `node_contract_ifc` (:257) | `isRaftNodeIfc` with Tick `⧗ 1`, ReadIndex credit, ApplyConfChange guarded by `dyn = false ∨`; `rnStopOk` | Advance over `nodeConfig + confAt + skippedIn`; Tick and ReadIndex with no credit; ApplyConfChange unconditional; no `rnStopOk` |
| `node_contract_propose` (:272) | `propErr` | `propErrS` (only if `raftPropose` exposes it) |
| `node_contract_memstor` (:280) | `isRNMemStor`'s Append over the old receipt | `appendReceipt … a` (the batch's committed prefix to freeze) |
| `read_raft` (:244) | `isReadRaft` with `srvRdCred` | Same statement; the credit is gone from `isReadRaft` |
| `applyAll_model` (:206) | Documented "under raft's no-snapshot contract" | Holds with snapshots (same statement; docstring) |
| `server_built_gap_on`, `server_start(_on)`, `server_run(_on)` (:2195/2223/1814/1827) | — | Only their composed premises (`isServerBuilt`/`srvBuildGap`) move. `rnSnapOnce` is to be rechecked. |
| `snapshotIfNeededAndCompactRaftLog.spec`/`specOn` (`ModeSpecs:50-90`, linked) | `1 ≤ γs.cap`, `ai ≤ w` ("no snapshot installed"), `srvSnapState`, `memFloorAtLeast` | `srvStorAp` (§4b(1)) and the `raftAdvancedC` fact |

**Downstream, not in this repair's scope:** `examples/common` and the eight server-based examples (`putget`, `putget3`,
`watchkv`, `authkv`, `linkv3p`, `linkvtxn`, `cachekv`, `k8setcd3`) consume `NewServer`'s statements and the allocation
(`common/Alloc.lean`, `Alloc3.lean`, `newServer.lean`). They break when those statements change, and are repaired after
the server (the memory note "raft first").

---

## 3. Gap table: examples/kv (lean's tree)

Lean changed kv only trivially since the merge base (4 files, 21 lines: `Check`, `Model`, `NewStorage`,
`Storage__InitialState`). kv's Go needs **no change** under D4(a). kv calls only `RestartNode` (`examples/kv/cluster.go:150`),
never `StartNode`. Its storage wrapper already answers the voters' ConfState (`kv.go:59-74`). No node is stopped. One
goroutine writes the storage: `run` calls `ApplySnapshot`/`CreateSnapshot`/`Compact` at `kv.go:274,295,298`.

| Cause | Files | Kind | What to reuse from kvreconf |
|---|---|---|---|
| **Old storage vocabulary** | `K/Defs.lean:100-232`, `KVStorageInstance` (385), `Storage__Snapshot` (64+91), `Storage__InitialState` (53+66), `NewStorage` (45+51), `Lemmas.lean:256` `kvStor_register`, `SnapData.lean:104-128` | Reproof, mostly copied | `R/KvrStorage.lean` (454), `R/KvrStorageApi.lean` (471: promoted methods, `kvrStorage_isStorage`, `kvr_bootStorage`, `kvrStor_alloc`, `kvrJ`), `Storage__Snapshot`/`InitialState` |
| **Conf changes** (`CCShrink`, `kvRule`, `RmShrink`, `cluster_alloc_rule`) | `Defs.lean:282-306,461-510`, `Reconf` (357), `Lemmas.lean:693` `kv_ccAu`, `:832/:863`, `Alloc` (99), `Spec/kv/KV__RemoveMember` | Medium | `Rule.lean`, `ConfStep.lean`, `ApplyConfLemmas.lean`, `SnapMake.lean`. Delete `Reconf.lean:306`'s `CreateSnapshot.unifiedSpec_tok_of`. |
| **Allocation and start** | `StartCluster` (504) | Reproof of the middle | `R/StartCluster.lean` (338) |
| **The Ready loop** (`memSnapTok`, `memStorCert`, `unifiedSpec`s, the `MemstorageAU` import, old `readySnap`/`advReceipt`, `nodeRunning`) | `KV__run` (903), `Spec/kv/KV__run`, `New` (58+95) | Reproof of `run`; `New` light | `Replica__run` (590) with `RunInv`/`RunAppend`/`RunApply`/`RunBatch`/`RunFrozen`/`RunSnap`, `Replica__maybeSnapshot`, `Replica__maybeCompact`, `frozenTo`, `appNode` |
| **Transport** (`NetMsgOk`, `tickCredit`) | `Cluster.lean:117-125,163-252`, `deliver` (262), `transfers__take` (42+70), `tick` | Light to medium | `Cluster__step`, `Cluster__deliver` |
| **Credits and modes** | `KV__Read` (Spec, and Proof 168), `Defs.lean:532` (`#Hxfer`), `Spec/kv/New`, `KV__TransferLeadership` (50), `KV__do` (150), `KV__RemoveMember` (82) | Light | `Replica__read`, `Replica__propose` |
| **Linking** | `Link.lean` (`etc/gen-link.py --kv`), `Results.lean`, `Adequacy*` (light) | Light | `R/Results.lean` |

Expected to stay as they are, if `runOwn` and `lockInv` keep their shape: `KV__apply`, `KV__answer`, `KV__install`,
`KV__Put`/`Get`/`Append`, `Base`, `Model*`, `Check`, `Gen`, `Main`, and the codecs.

**kv's exported results.**
- `kv_porcupine_safe` **keeps its statement**: `Main` reaches only `StartCluster`, `Check` and `Put`/`Get`/`Append` (`check.go:137-138`).
- `kv_Main`, `kv_Check`, `kv_StartCluster` and `kv_regLb_current` keep their text.
- Changes:
  - `kv_Read`: `readCredit` goes;
  - `kv_New`, `kv_run`: no `leaderTransferOn`, new `runStor`, `+ nodeRunning`;
  - `kv_NewStorage`: new post;
  - `kv_storage_isStorage`: becomes `isStorage γ id`;
  - `kv_storage_initialState` is replaced by `kv_bootStorage`;
  - `kv_RemoveMember`: `RmShrink` redefined (D4);
  - `rkvInv_alloc`/`kvStorInv_alloc`, if the registry's record changes.
- `kv_Put`/`Get`/`Append`/`TransferLeadership` keep their text; their meaning moves with `isKV`.

---

## 4. Invariant design

### 4a. Raft work the clients need first (R-items, each a raft public change: escalate)

- **R1. Shared MemoryStorage snapshot token** (the user's design input).
  - `memSnapExact` goes. A new `memSnapLb γs i` (stored index `≥ i`): persistent, timeless, with `memSnapLb_mono`.
  - `CreateSnapshot i` gives `memSnapLb i` on both outcomes. The client's additions:
    - **`cs ≠ nil` required** (`oc = some`): `memSnapCreated` uses the stored ConfState when `cs = nil`, which a shared token cannot know. Etcd always passes a non-nil `ep.confState` (`run` panics otherwise, `server.go:809-810`; also `ApplyConfChange`'s result and the snapshot's ConfState). kvreconf passes its `r.cs`.
    - ErrSnapOutOfDate also gives `memSnapLb i` and the data back.
  - `Compact x`: `memSnapLb x ∗ (memLog x □ [e] ∨ memCompacted x) ∗ J.B x`; post `memCompacted x`.
  - `ApplySnapshot`: no token in the pre; post `memSnapLb s ∗ memCompacted s ∗ memLog s □ [dummy] ∗ memEnd (s+1)`. Its success is proved inside the invariant: stored snapshots sit at frozen indices below any lent range.
  - **`Snapshot()` exactness at index 0**: when the index is 0, `sv = memSnapEmpty`. True: only the initial snapshot has index 0, because `ApplySnapshot`/`CreateSnapshot` need index > 0. `ownSnapM` must also give non-nil Metadata/ConfState pointers. The server's `run` builds `ep` from the boot `Snapshot()` and panics on nil (`server.go:754,802-811`).
  - kvreconf moves its snapshots into a separate goroutine first, as the template, and is re-proved over R1.
- **R2. `readyFits` from `cluster_alloc`.** Add `readyFits γ N` (or `γ.bootLen = 0` with a law to `readyFits`) to `cluster_alloc`'s post (and to D1(a)'s allocation). The server needs it for `Append`'s bound through `readyRest_fits`. Small.
- **R3 (optional, cheap). `nodeConfig_confAt : nodeConfig n γ N v ⊢ confAt γ v.applied v.membership`** (Q6 of the gap design). Without it, the server's and kv's run invariants carry `confAt` beside `nodeConfig` and re-derive it at every step (`confAt_decided`/`confAt_noConf`, and Advance's post at a snapshot). With it, `rnCfgAt` and kv's `appNode` lose a conjunct. Both sides are in `InvApi`.
- **R4 (if D2(a)). The MsgSnap sender's witnesses.**
  1. `sentMsg_replaceSnapshot` needs `sv.index ≤ sv'.index` (the new merged index). In Go, a MsgSnap from Ready k+1 carries a snapshot the storage held. That is either the job's own `CreateSnapshot` (`≤ ai`), or `ApplySnapshot(k)`; and Ready k+1's messages exist only once `applyAll(k)` has set `appliedi = s` (the `notifyc` hand-off, below). Raft's API cannot derive this. Either `sentMsg_snapshot` for `src = id` also gives a persistent "the node's storage returned `sv`" witness (tied to `isStorage`'s `Snapshot()`, so to `memSnapLb`), or raft drops the premise if its progress invariant does not need it (ask the raft proof's owner).
  2. A Ready term witness: a non-empty `hs.Term` in a `Ready` is raft's term, with a committed index. This gives `committedAtTerm γ N T c`, so that the merge at `m.Term == raftTerm` (D22a) yields `appliedi ≤ c`. Today it is `True` at `InvRaftNode:863` (D22 S-b's planned `rnRtOk`).

  About 200-400 raft lines.
- **R5 (if D1(a)). StartNode.** A decision-cluster allocation with a bootstrap log, with these changes:
  - `UniNames`' "empty boot log" clause relaxed to "no empty `ConfChangeV2`" (`InvApiDec.lean:102-106`);
  - the boot conf entries decided `apply` at allocation;
  - posts `isCommittedLogLb γ boot`, `readyFits` (R2) and a per-node boot token;
  - a unified `StartNode.spec` over `RawNode.Bootstrap` (kept) and a restored `setupNode`.

  About 1-2k lines (P8 of the gap design). The server keeps its boot-log membership model (`restModel c0 boot`, `srvDec`).

### 4b. The server's invariants, final form

**(0) `SrvRaft` and the cluster** (`P/SrvRaftLog.lean:74`, `:644`).
- `SrvRaft = {cl, vs, boot (D1(a)), reg, snapLoc, log, fresh, props, fired, rdFresh, pend}`.
  - `dyn` goes.
  - `dec` becomes a server-defined `srvRule c0 boot : ConfRule := fun pre _ e => if e.type = 1 then (ccDecodeV1 e.data).map (.v1 ∘ ccRaftEff (restModel c0 boot (withIdx pre)).bk) else none`, which is `srvDec` (`InvCfgView.lean:71`) re-typed. A `ConfChangeV2` gives `skip`; the server proposes none.
- `srvClusterOk γ := isCluster cl srvClusterN ∗ confPolicy cl srvConfN (srvRule …) ∗ readyFits cl srvClusterN ∗ ⌜cl.dup = false⌝ ∗ inv srvSnapsN (∃ S, ownSnapsMade cl S)`.
- Why:
  - `isCluster` replaces both families.
  - `confPolicy` (from `cluster_alloc`'s `ownConfDecisions ∅` by `confPolicy_alloc`) makes every member decide identically with no owner afterwards. This is what `ApplyConfChange`'s `confDecided` needs.
  - `readyFits` is needed for `Append` (R2).
  - The registry is needed for `snapshotCert_make`, used both by `CreateSnapshot`'s `J.SV` and by the merged MsgSnap. It is cluster-wide and opened under `↑srvClusterN`; `srvSnapsN` sits beside `srvLogN`. It needs no content invariant: etcd's raft snapshot data is `nil` (the data travels as the image certificate, `srvImage`).
  - It is allocated in `NewServer` beside `srvLogInv_alloc` (`SrvRaftLog.lean:1892`).
- What goes: `srvRdCred`/`srvRdFreshInv`'s credit, `srv_sentMsg_notSnap`, `srv_readySnap_none`.

**(1) Conf changes** (`InvCfgView`, `NodeBridge`).
- The server always decides `apply`. In Go, a failed `ValidateConfigurationChange` sets `cc.NodeID = raft.None` and still calls `ApplyConfChange` (`server.go:2004-2016`): an `apply` with no effect (`Membership.applyChange_nodeZero`). So `o = o' = .v1 (ccRaftEff bk m)`.
- The contract `raftApplyCC γs n nd`:
  - pure premise `srvCCPre` (`InvCfgView:111`, rule-based, no `dec`);
  - pre: `ownConfChangeI ∗ nodeConfig v ∗ confAt γ v.applied v.membership ∗ deliveredLogLb l`;
  - the bridge proves `confDecided` by `confPolicy_decide` (with `deliveredLogLb_committed`), and `skippedIn` by `skippedIn_noConf` (the server proposes no V2; the boot log is v1);
  - post: `(csPts ∗ nodeConfig ⟨k+1, m'⟩ ∗ confAt γ (k+1) m') ∨ (⌜csp = null⌝ ∗ nodeStopped)`. The second disjunct is refuted by the loop's `nodeRunning` fraction (`nodeRunning_stopped`).
- Under D3 (static membership) every decided step keeps the boot membership, so `confAt` stays `c0`.
- `shouldApplyV3 = false` replays skip `ApplyConfChange` (`server.go:2022-2024`). A rule cannot express that local skip, so the scope stays "fresh start, `c0 ≤ ai0`" (already `EtcdServer__run.lean`'s `hdvs`).

**(2) The transport** (`InvNet`, `InvBuild.srvNet`).
- `srvNet` (`InvBuild:136`): `P := ∃ sid, sentMsg γ N sid st`, `O := msgCredits γ N st`. `dup` is by `msgCredits_intro` for non-`MsgProp`.
- The `once` class shrinks to `MsgProp`: a forwarded proposal's `msgCredits` carries its update and is delivered at most once (rafthttp, as today).
- `stepIn_of_recv` becomes `stepIn_intro` directly (no `srvClusterOk`, no `NetMsgOk`). A received `MsgSnap` now reaches `Process` and `snapshotHandler__ServeHTTP`; `stepIn` needs no premise of its own for it.

**(3) The raft loop's payloads** (`InvRaftNode`).
- `rnMsgR` and `rnSnapMsg` become real: a MsgSnap from `rd.Messages` goes to `msgSnapC`, or is dropped when the channel is full (`raft.go:373-383`), with its `sentMsg`.
- `rnReadyData` admits `rd.Snapshot ≠ null`.
- The new payloads, sent through the new `notifyc` protocol (below):
  - `rnApN`: the batch's committed part. Its frozen entries come from `ceFrozen` or from `appendReceipt`'s `a`, plus the `deliveredLogLb` and the configuration view. `rnApGive` hands the `deliveredLogLb` **unconditionally** (today only when `rnHands`, `InvRaftNode:901`).
  - `rnApSnap`: the snapshot clone (`ownSnapM … discard`), `snapshotCert`, `memCompacted s`, `memLog s □ [dummy]`.
- **`notifyc` with two receives** for a snapshot batch.
  - Go: the raft loop sends #1 before `ApplySnapshot` (`raft.go:274,277`) and #2 after `Append` (`:302`/`:327`); `applySnapshot` takes #1 (`server.go:1037`); `notifyc` has capacity 1. So #2 blocks until `applyAll(k)` has started.
  - This is a variant of `isNotify`. It is where the "snapshot ceiling" argument for R4.1 lives: messages of Ready k+1 exist only after `applyAll(k)` set `appliedi`.
  - The ghost ceiling `max(ai, the index of a snapshot batch not yet started)` belongs to the server; the two-receive notify could be a reusable lemma.
- `isRaftNodeIfc`:
  - Advance over `advReceipt` and (`skippedIn` | `snapshotCert`), returning `nodeAppliedLb`;
  - Tick `{{True}}`;
  - ReadIndex with no credit;
  - ApplyConfChange as in (1);
  - Stop with `nodeRunning 1` (replacing `rnStopOk`/`rnStopOkStarted`: the loop holds `nodeRunning 1` from the start and gives it to `node.Stop` in `onStop`).

**(4) The apply hand-off: `raftAdvancedC`** (`raftNode__start:403,634`; `InvRaftNode:862,920`).
- Per batch, the loop allocates a stop-channel with `P := nodeAppliedLb γ id |pre ++ F ++ ce|` (was `memFloorAtLeast`), and closes it after `node.Advance` with Advance's post. `nodeAppliedLb` is persistent and timeless.
- On a snapshot batch, `P = nodeAppliedLb … s`.
- If Advance answers `nodeStopped`: refuted by `nodeRunning` (the loop holds a fraction).
- Every close path stays (the proof closes on four paths: 634, 684, 737, 782).
- `applyAll` receives `P` from the closed channel before `snapshotIfNeededAndCompactRaftLog` (the fork's wait, translation l.2546). That is `Compact`'s `J.B`. On the `stopping` branch it does not compact.

**(5) The apply thread's storage state** `srvStorAp ep ms γs ai cs`. This replaces `srvSnapState`'s `memSnapRO`/`memKey ak`/`γss`/`memTokShared` and `memFloorAtLeast` with persistent facts only, no exclusive storage resource. At applied index `ai = |pre ++ A|`:
- `memSnapLb γs dsi` for the disk and memory snapshot indices `≤ ai`;
- a frozen entry `memLog ai □ [e]` with `e.Term = ep.appliedt`, or `memCompacted ai` and the snapshot's dummy;
- `storDL γ id ai` (from the handed `deliveredLogLb`);
- `∃ m, confAt γ ai m ∗ ⌜confStateIs cs m⌝` with `ep.confState = cs ≠ nil`;
- `srvRLogLb A`.

Why it holds: the frozen entry comes from the Ready's `ceFrozen`, or from Advance's receipt `a` for committed entries in `es`; it reaches the job through `rnApN`. `confAt` comes from (1)'s decisions along the log, or from `Advance`/`snapshotCert_made` after a snapshot. It is re-formed at `ai = s` after a snapshot batch from `rnApSnap`.

**(6) `CreateSnapshot`** (`SnapTake`, `SnapTakeProof`, `EtcdServer__snapshot`), from (5):
- `isCommittedLogLb (srvLE A)` with last term `appliedt`;
- `confAt γ ai m`, then `confAt_valid` and `Membership.Valid.snapListsOk` (needs `0 ∉ ids`, learners and voters disjoint, `< 2^61` ids, `ai < 2^61`);
- `snapshotCert_make` in the registry, then `snapshotCert_valid` (`0 < ai`: the snapshot trigger);
- `J.DL = storDL` from the `deliveredLogLb`; `cs ≠ nil` (R1).

Post: `memSnapLb ai` on both outcomes.

**(7) `Compact`** (`EtcdServer__compactRaftLog`, `snapshotIfNeeded`). `compacti ≤ ai` (`compacti = appliedi - SnapshotCatchUpEntries`, or 1; `server.go:2140-2157`). It needs:
- `memSnapLb compacti` from `CreateSnapshot`'s post by mono (`compactRaftLog` runs after `snapshot()`, `server.go:1217-1218`);
- the frozen entry or `memCompacted` at `compacti`, from (5) by mono;
- `J.B` = `nodeAppliedLb γ id ai` from (4), by `nodeAppliedLb_mono`.

`ErrCompacted` is benign.

**(8) The raft loop's `ApplySnapshot`** (`raftNode.start`, `raft.go:256-282`).
- From `readySnap (some l)`: the ranges from `k ≤ s` with the end, and `snapGiven γ id s`, which gives `J.B s` and `J.DL s`. `snapshotCert` gives `J.SV` through `snapshotCert_valid`, and `s < 2^61` is a conjunct.
- No token (R1). Its post, `memLog_nil` and `Append` make `snapReceipt`.
- Advance then gives `nodeAppliedLb … s ∗ confAt γ s m ∗ confStateIs`.

**ApplySnapshot really is concurrent with CreateSnapshot/Compact.** The raft loop's `ApplySnapshot` for Ready k+1 races the job's `CreateSnapshot`/`Compact` for batch k:
- the FIFO scheduler does not wait (`server.go:839-841`), and `notifyc` #1 is sent before `ApplySnapshot`;
- Go acknowledges the race: "raft might have already got a newer snapshot" (`server.go:2104-2108`), and `ErrCompacted` at `2152-2157`;
- it is reproduced in `notes/j3-overlap-test/output.txt`.

So the shared `memSnapLb` of R1 is necessary, not just convenient; no hand-off of an exclusive token can work.

**(9) The MsgSnap sender (D2(a))** (`EtcdServer__applyAll`, `createMergedSnapshotMessage`, `sendMergedSnap`, `SnapSendBranch`, rafthttp `snapshotSender__send`).
- `applyAll`'s non-blocking read of `msgSnapC` gets the `sentMsg` (from `rnSnapMsg`), whose `sentMsg_snapshot` gives `snapshotCert`.
- When `m.Term == raftTerm`: `createMergedSnapshotMessage(m, appliedt, appliedi, confState)` (`snapshot_merge.go:32-53`) gets the merged `snapshotCert` from (6)'s registry and `sentMsg_replaceSnapshot`, with:
  - `isCommittedLogLb` of length `appliedi` (from (5));
  - `committedAtTerm` (R4.2);
  - `sv.index ≤ appliedi` (R4.1 and the ceiling in (3)).

The receiver: `Process`/`snapshotHandler__ServeHTTP` step it with `stepIn_intro`. Applying a received snapshot is (8) plus the already-proved `applySnapshot.specSnap`/`SnapApply*`.

**(10) Boot.**
- D1(a): `NewMemoryStorage`'s `memLog 0 □ [e0]`, `memEnd 1`, `memStorLock`, `memStorFresh`, `memStorMeta`. Register `memStorReg` (`memStorRegAuth ∅`, kept). Raft's new StartNode takes the storage as its spec will say: presumably `isStorage` after `memStorInv_alloc`, with `InitialState`'s triple over the fresh tokens, as `bootStorage` does. `run`'s `Snapshot()` returns `memSnapEmpty` (R1's exactness), `ep = (0, 0, empty)`, and the boot AddNode entries set `ep.confState` to the peers before any snapshot (`CreateSnapshot` needs `ai > 10000`).
- D1(b) (not recommended): a wrapper Storage. It needs interconversion between its `StorageModel` and `ms`'s `memLog`/`memEnd`, because `raftNode.raftStorage` is the concrete `*MemoryStorage`. It also needs fork changes to seed `ep.confState` and the backend's members (above).

### 4c. kv's invariants, final form

- **Cluster.** `kvCluster := isCluster ∗ confPolicy γ kvConfN kvRule ∗ confAt γ 0 kvMembership ∗ kvSnapInv`. `kvRule _ _ e = ccDecode e` always decides `apply`: under D4(a) every `RemoveMember` id is a non-voter, so `applyChange_removeAbsent`/`_nodeZero` (`I/InvNode.txt:138,276`) keep `kvMembership`. `skippedIn` holds by `skippedIn_noConf`.
- **Snapshot registry.** `kvSnapInv` over `ownSnapsMade` (`K/Defs.lean:494`), each record weakened to kvreconf's `kvrSnapRecOk`: `∃ L, isCommittedLogLb L ∗ confAt |L| s.conf ∗ ⌜|L| = s.index ∧ kvSnapOk L s.data⌝`. `s.conf = kvMembership` and `NoConfChangeIn` go.
- **The run loop's new predicate**, beside `runOwn` so that `apply`/`answer`/`install` keep their proofs:
  - kvreconf's `appNode`: `nodeConfig v ∗ deliveredLogLb l ∗ skippedIn l v.applied k`;
  - `confAt γ |ap| m` with `¬reconf → m = kvMembership` (or R3);
  - `nodeRunning n γ N 1`, which refutes the `nodeStopped` disjuncts; kv never calls `Stop`;
  - `frozenTo` (kvreconf's `DefsCluster.lean:129`) for the frozen entries.
- **Storage.** `isStorage γ id st` by a copy of `kvrStorage_isStorage`. `kv_bootStorage` replaces `kv_storage_initialState`:
  - the frame `R` holds `NewMemoryStorage`'s tokens;
  - FirstIndex/LastIndex are the promoted methods;
  - kv's `InitialState` (`kv.go:72-74`) never calls `MemoryStorage.InitialState`, so `memStorInv_alloc` runs inside `bootStorage`'s `|={⊤}=>` (simpler than kvreconf);
  - `csPts discard` comes from the persisted voters.

  kv's `Snapshot` wrapper (`kv.go:79-85`, a snapshot with `ErrSnapshotTemporarilyUnavailable`) is admitted by `isStorageP`'s Snapshot clause (`I/InvStorage.txt:346-361`).
- **`KV__run`, per Ready.**
  - `readyRest_indices`/`_ceInBatch` give `applied = |delivered|`.
  - With a snapshot, `readySnap … id` gives `snapshotCert` (then `_valid` for `J.SV`), `snapGiven` (`J.B`/`J.DL`) and the ranges for `ApplySnapshot`.
  - `Advance` takes `advReceipt st.storage |delivered| es L` and gives `nodeAppliedLb |delivered|`.
  - `CreateSnapshot(applied, {Voters}, data)` (`kv.go:295`, `cs ≠ nil`) needs `snapshotCert_make` (committed `ap`, `confAt |ap| kvMembership`, `kvConfState_is` `Reconf.lean:89`, `snapListsOk_voters` `KV__run.lean:98`), `J.DL` from `deliveredLogLb`, and the frozen entry at `applied` (`frozenTo`).
  - Under R1 kv has one writer, so `runStor` keeps no token: `CreateSnapshot`'s `memSnapLb applied` gives, by mono, `memSnapLb (applied-10)` for `Compact` (`kv.go:298`), with `nodeAppliedLb` and the frozen entry or `memCompacted`.
- **Allocation.** `cluster_alloc kvRaftN [1,2,3] (dup := false)`. Its post feeds the store:
  - `ownCommittedOps`/`ownReadCtxs` go to `rkvInv_alloc`;
  - `ownConfDecisions ∅` goes to `confPolicy_alloc`;
  - `ownSnapsMade []` goes to `kvSnapInv_alloc`;
  - each `nodeFounder` goes to `RestartNode`;
  - `joinAuth` is dropped.

  `RestartNode`'s premises: `cluster.go:150-160` (config) and `kv.go:73` (voters); `HsEmpty` because kv returns `HardState{}`.
- **Transport.**
  - `deliver` proves `stepIn` by `stepIn_intro`: routed by `To`, `msgPtsC` from the copy (`cluster.go:113-122`), and `msgCredits` handed through from the Ready (`dup = false`, each message delivered at most once).
  - The `deliverable` lemmas become unneeded.
  - `transfers.take`'s post becomes `True`; `tick` takes no credit.
- **Client operations.**
  - `KV.Read` drops `readCredit`, and `ReadIndex` answers `nodeErrS`.
  - `TransferLeadership` needs only `isKV`.
  - `RemoveMember` is `kv_ccAu` over `ops ++ opsOf [entry]`, with the redefined `RmShrink`.
  - `do`: `Propose` with `propErrS` and a plain AU.

---

## 5. Proof plan: each function reproved once

The rule that makes "at most once" possible: **freeze every shared statement first**, the client invariants and specs
above, as a statement phase with `sorry` bodies, reviewed. Then prove each function exactly once against the frozen
statements. A track that finds a frozen statement false stops and escalates; it does not patch it locally. Raft's
R-items come before the client statement phase, because the client statements are written over them.

**Stage 0: merge lean (in progress) and rebuild raft under the new pin.**
- Lean moved Perennial `6b58510f9` → `ad74ee4f6` ("uniform function results, range over functions") and regenerated raft's translation: `Code`/`GeneratedProof` for raft, 4724+/1766−. It also touched 37 raft proof files (pin adaptations: MemoryStorage proofs, `newLogWithSize`, `stepLeader/Rest`, `Config__Clone`, `confchange`, `raftpb` getters).
- Repair's raft is the a2 fork's translation with raft-final's rewritten proofs, so the merge must:
  - re-translate raft a2 under the new pin (`etc/goose.py --project raft --src raft=.lake/raft-fork`);
  - re-port lean's 37 pin adaptations onto raft-final's versions (many of those files were rewritten);
  - rebuild raft's `Link`/`Linked`/`Results` and kvreconf.
- **Risk:** this is a raft-wide re-check (hundreds of new proofs) under a pin that changes function results. Budget a dedicated track. It precedes everything.

**Stage R: raft work** (after D1/D2; one raft agent or two file-disjoint ones). Sizes:
- R1 (MemoryStorage shared token, `Snapshot` exactness, `cs ≠ nil`), 300-600, then kvreconf re-proved over it (its snapshot goroutine first), ~300-500;
- R2, ~50;
- R3, ~50-100;
- R4, 200-400;
- R5, 1-2k.

Freeze and regenerate `interface/`.

**Stage F: the client statements** (one agent per client, reviewed: a `spec-reviewer` pass).
- Server: `SrvRaft`/`srvClusterOk`/`srvRule`; `rnCfgAt` with `confAt`; `raftApplyCC`; `isRaftNodeIfc` (all clauses); `srvNet`; `rnMsgR`/`rnSnapMsg`/`rnApN`/`rnApSnap`/`rnReadySnap` and the two-receive notify; the `raftAdvancedC` payload; `srvStorAp`; `isRNMemStor`; `NodeStartSpec`; the allocation's post; one shared premise bundle for the three `NewServer` statements, then the statements; the `ModeSpecs` restatements; every changed internal spec (`applyConfChange`, `snapshot`, `compactRaftLog`, `snapshotIfNeeded`, `applyAll`, `raftNode.start`, `processMessages`, `newRaftNode`, `NewServerAlloc*`).
- kv: T0 below (`Defs`, `Reconf`, `Alloc`, `Cluster`, the conf lemmas) plus the changed spec files.
- The trusted-statement diffs (2c, 3) go to the user.

**Stage P: proofs.** At most 3-4 helpers at a time, **in one worktree**, file-disjoint, each checking with
`etc/lean-check.py` against the frozen statements. Disk: 39 GB free, ~18 GB per worktree, so at most one extra
worktree. A commit per lemma or function; `lake build` of the whole only at track ends, by the integrator.

| Wave | Track | Files | Size | Needs |
|---|---|---|---|---|
| 1 | **K-a** kv storage and transport | `KVStorageInstance`, `NewStorage`, `Storage__Snapshot`, `Storage__InitialState`, `kv_bootStorage`; `deliver`, `transfers__take`, `tick`, `Cluster` lemmas | ~1.4k (mostly copied) | F (kv), R1 |
| 1 | **S-A** server net, read and errors | `InvNet`, `InvBuild.srvNet`, `BuildGap`, `NodeApiLink`, `NodeBridge`'s error lemmas, `read/`, `raftNode__ReadIndex`, `raftNode__tick`, `EtcdServer__Process`, rafthttp handlers, `ProposeOn`/`processInternalRaftRequestOnce` (`propErrS`) | ~0.8k, light | F (server) |
| 1 | **S-B** server conf changes | `InvCfgView`, `EtcdServer__applyConfChange`, `InvRaftLoop`, `NodeBridge`'s `raftApplyCC`/`isRaftNodeIfc_of_isNode` | ~1.5k | F |
| 1 | **S-C** raft loop | `InvRaftNode`'s lemmas, `raftNode__start`, `raftNode__processMessages` | ~1.2k | F, R1, R4 |
| 2 | **K-b** kv client ops, then run | `KV__do`, `KV__Read`, `KV__RemoveMember`, `KV__TransferLeadership`, `kv_ccAu`/`kv_propAu`; then `KV__run` (split into lemma modules copied from kvreconf's `Run*`), `New` | ~1.6k | K-a |
| 2 | **S-D** apply thread and storage | `InvApplyAll`, `SnapTake`/`SnapTakeProof`/`EtcdServer__snapshot`, `compactRaftLog`, `snapshotIfNeeded`, `EtcdServer__applyAll`, `SnapSendBranch`/`InvSnapSend`/`SnapRecvFacts`/`createMergedSnapshotMessage`/`sendMergedSnap`/rafthttp snapshot files (rewired), `SnapApply*` premises | ~2.5k | F, R1, R4 |
| 3 | **S-E** boot, allocation and top | `NodeStart`, `bootstrappedRaft__newRaftNode`, `newRaftNode`, `InvNodeStart`, `NewServerAlloc`, `NewServerAllocOn`, `BuildAlloc`, `InvBoot`, `P/NewServer`, `EtcdServer__run`, `InvRun`/`InvStart`/`ServerOn`/`StartOn`/`RunOn`/`InvApRes` (light) | ~2.5-3k | R5 (or D1(b)), and F only: the statements of everything else, not the proofs |
| 3 | **K-c** kv start and link | `StartCluster`, `Link.lean` (gen-link `--kv`), `Results`, `Adequacy*` | ~0.5k | K-b |
| 4 | **Link** | server `Link.lean` (`etc/gen-link.py --server`, `etc/link-lean-first-server.txt`), `Results.lean`, read `Link`/`Results`; `etc/tcb-report.py --check` (expect `ccDecodeV2_nil`, the R-items' axioms: none planned); `interface/` regenerated; then the downstream server examples, as a separate repair | — | everything |

S-E can start in wave 2 if the R5 statement is frozen, because it depends only on the other tracks' statements. Totals,
roughly: server 9-11k lines touched (of which ~4k new proof), kv ~3.5-4k, raft (R1-R5) 2-3.5k. Under D1(b) and D4(b),
add the fork's Go changes, re-translation and their proofs instead of R5.

---

## 6. Open questions and risks

1. **D1 StartNode, D2 MsgSnap, D3 membership scope, D4 kv RemoveMember, D5 trusted statements** (section 0). D1 and D2 block Stage R.
2. **R4.1**: can raft drop `sentMsg_replaceSnapshot`'s `sv.index ≤ sv'.index` premise, or must it export a stored-snapshot witness? Ask the raft proof's owner; it decides R4's size.
3. **Stage 0 risk**: raft-final's whole proof under the new Perennial pin and re-translation. It is untried. If it is large, an alternative is to merge lean into `repair` for the clients only and bump raft's pin separately. That is the user's call; the coordinator asked for the merge.
4. **New ghost state** to escalate:
   - raft: `memSnapLb` (R1, user-designed), R4's witness, R5's boot token;
   - server: `inv srvSnapsN (∃ S, ownSnapsMade γ S)` (internal) and the snapshot-ceiling ghost in the two-receive notify.
5. **`NewServer`'s three statements**: factor a shared premise bundle in Stage F, or every change is made three times.
6. **Liveness only, not a safety bug**: `processMessages` drops a MsgSnap when `msgSnapC` is full and never calls `ReportSnapshot` (`raft.go:378-382`), so the follower can stay in snapshot state. Worth an `issues/` entry only if someone wants a liveness note.
7. **kv inherits `issues/raft-remove-last-voter-panic.md`** through the exported `RemoveMember` (not `Main`). Under D4(a) the premise sidesteps it; this is already recorded.
8. No new Go bug was found on the paths studied. The fork's three Go facts (2b) must be re-confirmed against the pinned translation once lean is merged.

## User decisions (2026-10-30), binding

- D1: (a) — StartNode built in raft (an allocation with a bootstrap log + a unified StartNode spec; R5).
- D2: (i) — no snapshot path in the server proof, without modes: the server owns `ownSnapsMade γ []` for
  good, so every snapshot certificate/validity (and so every MsgSnap, and Ready's snapshot) implies False
  (`snapMade_elem`); `CreateSnapshot`/`Compact` are made unreachable by a NewServer premise
  `receiptBound ≤ SnapshotCount` (the run never reaches a snapshot), REPLACING the old
  `receiptBound ≤ SnapshotCatchUpEntries`. The sender/receiver proofs stay dead; R4 is not needed.
- D3: static membership after boot (the server need not support membership changes for now).
- D4: remove examples/kv's `RemoveMember` — its Go code, spec and proof (kv_porcupine_safe doesn't reach it);
  note in the plan that it can return later with kvreconf's validConf guard (verified-code count drops by it;
  the user approved).
- D5: the §2c trusted-statement changes approved (with D2(i)'s premise in place of the run-length one).
- Stage P: ONE pass — stage F freezes every shared statement first; then all tracks start together, each
  function proved exactly once; minor local statement tweaks during proofs are logged and reported.
- R1 (memSnapLb, non-nil cs, Snapshot() exactly empty at index 0 on a never-snapshotted storage), R2
  (cluster_alloc gives readyFits), R3 (nodeConfig ⊢ confAt), R5 (StartNode): approved; R4 dropped (D2(i)).
- Stage P order (user, 2026-10-30): with limited parallelism, start first the tracks most likely to
  influence other proofs — those whose proofs exercise the shared invariants hardest and so are most
  likely to force an invariant/statement tweak: the server's raft loop (raftNode start/run: Ready
  hand-out, Append, Advance, the raftAdvancedC hand-off), the server's apply thread and storage
  (applyAll, the boot/InitialState wrapper), the allocation/NewServer composition, and kv's run loop;
  leaf and client-operation tracks (net/read/errors, kv client ops, conf-change wrappers) after, as
  slots free.
- D2 REVISED (user, 2026-10-30: "Do (D) for now"; D2(i) was false against etcd's Go: in-memory snapshots
  every memorySnapshotCount = 100 entries and ForceSnapshot reach CreateSnapshot whatever SnapshotCount):
  the server registers its snapshots (ownSnapsMade in an invariant; EtcdServer.snapshot proved via specFull,
  no axiom); NewServer keeps the old premise receiptBound ≤ SnapshotCatchUpEntries (compactRaftLog never
  calls Compact); a new raft law: a sent MsgSnap implies its sender's storage was compacted past 0; so,
  no member's storage ever being compacted, every MsgSnap and Ready snapshot implies False. The snapshot
  send/receive paths stay unverified for now (a later D2(a)).
- D2 REVISED AGAIN (user, 2026-10-30): "I'd rather introduce an axiom or sorry than introduce bogus ghost
  state … an axiom that we could plausibly prove later for the real proof … axioms that cover whatever
  happens when there *are* snapshots." So: the server registers its snapshots; snapshots, compaction,
  MsgSnap, ForceSnapshot are allowed; NO run-length premise; the snapshot-handling functions
  (EtcdServer.snapshot, the merged-MsgSnap send path, the rafthttp receive path, possibly applySnapshot)
  get temporary trust-boundary axioms stating their TRUE specs (to be proved after the merge into lean);
  raftNode.start's snapshot branch is proved. Supersedes D2(i), (D′), (a), and the cap route. The axiom
  statements go to the user for sign-off first.
- D2 refined (user, 2026-10-30): "Make the snapshot branches sorry's for now, but keep the rest of the
  proof as much as possible." → each snapshot-only code path closed by one marked `sorry`
  (SNAPSHOT-SORRY), non-snapshot paths proved; sorry preferred over new axioms and ghost state; snapshots
  registered; no run-length premise; the exact list in the plan ("Repair: snapshot sorries").

## Coordinator decisions while the user is away (2026-10-30)

- The SNAPSHOT-SORRY list and statement changes proposed by Stage F (branches A1-A5, snapshot-only
  functions B6-B9 with sorry bodies and true specs, the statement changes C: the registry
  `inv srvSnapsN (∃ S, ownSnapsMade cl S)`, real `rnSnapMsg`/`rnReadySnap`/`rnApSnap`, frozen entries
  through Advance's receipt and the raftAdvancedC payload, `srvSnapStor`, NewServer without any
  run-length premise) are ACCEPTED by the coordinator (logged for the user's later review), in line with
  the user's "snapshot branches sorry, rest proved as much as possible".
- Checkpointing: after each milestone, commit and push the plan state (this file, the plan's "Repair:"
  sections, STATUS.md).
