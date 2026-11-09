# Batch 2d: etcd's apply thread, raft node driver, consistent index, FIFO scheduler (report)

Author agent, 2026-11-09. Everything builds (`etc/specs-build.sh` on the batch's 66 modules: OK);
snippets: `cd examples && go vet ./specreq/{etcdserverapply,cindex,schedule}/` clean, `gofmt -l`
clean (the `//go:build ignore` files of `etcdserverapply/` are in-package code over unexported
members: gofmt-checked and read against the source, not type-checked: Go refuses an overlay into the
module cache).

## Files

`Spec/go_etcd_io/etcd/server/v3/etcdserver/` (namespace `EtcdServer`):
- `ApiApply.lean`: the vocabulary (below).
- The apply thread: `EtcdServer__{run, applyAll, applySnapshot, applyEntries, apply,
  applyEntryNormal, applyConfChange, snapshotIfNeededAndCompactRaftLog, shouldSnapshotToDisk,
  shouldSnapshotToMemory, snapshot, compactRaftLog, ForceSnapshot, createMergedSnapshotMessage,
  sendMergedSnap, revokeExpiredLeases}.lean`, `verifyConsistentIndexIsLatest.lean`,
  `newSnapshotReaderCloser.lean`.
- The server's atomics: `EtcdServer__{setAppliedIndex, getAppliedIndex, setCommittedIndex,
  getCommittedIndex, setTerm, getTerm, setLead, getLead}.lean`.
- The transport's inbound calls: `EtcdServer__{Process, ReportUnreachable, ReportSnapshot,
  IsIDRemoved}.lean`.
- The raft node driver (`raft.go`): `newRaftNode.lean`, `raftNode__{start, tick, advanceTicks,
  getLatestTickTs, processMessages, apply, ReadState, stop, onStop}.lean`, `updateCommittedIndex.lean`,
  and raft's methods promoted through the driver: `raftNode__{Propose, ReadIndex, Step,
  ReportUnreachable, ReportSnapshot, ApplyConfChange}.lean` (R1's statements at the driver).

`Spec/go_etcd_io/etcd/server/v3/etcdserver/cindex/` (namespace `Cindex`, new): `Api.lean`,
`NewConsistentIndex`, `consistentIndex__{ConsistentIndex, UnsafeConsistentIndex, SetConsistentIndex,
SetConsistentApplyingIndex, ConsistentApplyingIndex, UnsafeSave, SetBackend}`.

`Spec/go_etcd_io/etcd/pkg/v3/schedule/` (namespace `Schedule`, new): `Api.lean`, `NewFIFOScheduler`,
`NewJob`, `job__{Name, Do}`, `fifo__{Schedule, Stop, run, executeJob}`.

Snippets: `examples/specreq/etcdserverapply/` (`apply.go`: `ReqWriteAnswered`, `ReqAppliedRead`,
`ReqConfChangeAnswered`, `ReqReplayBelowCI`, `ReqNoSpaceAlarm`; `snapshot.go`: `ReqSnapshotCompact`,
`ReqMergedSnapshot`, `ReqInstallSnapshot`; `restart.go` (compiled, over the client):
`ReqRestartContinues`, `ReqCrashKeepsAnswered`, `ReqLeaseExpiry`; `raftnode.go`: `ReqReadIndex`,
`ReqPropose`, `ReqProcess`, `ReqDriverLoop`, `ReqWriteBeforeSend`), `examples/specreq/cindex/cindex.go`
(`ReqApplyMovesIndex`, `ReqReloadAfterSetBackend`, `ReqSaveInCommit`),
`examples/specreq/schedule/schedule.go` (`ReqFifoChain`, `ReqStopRunsPending`, `ReqCancelledCtx`).

## Exported vocabulary

`ApiApply.lean` (`EtcdServer`):
- `Names` (structure: `etcd : EtcdModel.Cluster`, `raft : Raft.Cluster`, `cfg : EnvCfg`, `hist`):
  the server-level names; `HistNames` opaque.
- Pure: `Progress` (applied index/term, disk/memory snapshot indices), `ApplyBatch` (`prev`, `ents`,
  `snap`, `term`) with `base`/`last`, `applyV3 ci i` (ShouldApplyV3); provisional 3a's `MemberCfg`,
  `applyStep mc σ e σ' res` (the apply's model, deterministic).
- Cluster level (shared with 2c, 2e, 3a): `histAt γ k σ` (pers: the model state after the committed
  log's first `k` entries), `answered γ k id res` (pers), `snapImage γ s` (pers: a raft snapshot's
  db image, at a committed point `≥ s.index`).
- Member: `srvNode s γ id` (pers, from `NewServer`), `srvStarted s γ id` (pers, from `start`),
  `srvApplied s γ k` (pers: applied the first `k`), `srvRunTok s γ id` (excl, `start` → `run`),
  `srvStopped s γ id` (excl, what a stopped member leaves), writers `appliedW`, `committedW`,
  `termW`, `leadW`, `forceSnapW`.
- Apply thread: `applyThread s γ ep p` (excl), `applyAt s γ ep p a c ai` (excl, inside `apply`'s loop).
- Driver: `isRaftNode r γ id n` (pers), `rnInit v γ id n`, `rnCfgOk cv γ id n` (excl),
  `rnLoop r`, `rnStopper r` (excl), `rnStopped r γ id` (excl), `readyHandlerOk rh s γ` (pers),
  `readyHandlerTok rh` (excl), `applyBatch r γ apv B ph` (excl), `nodeAdvanced r k`,
  `nodeSnapLb r k` (pers: R1's `appliedLb`/`storSnapLb` of the driver's node), `advancedAt r rac k`,
  `rnApplyc r ch`, `rnReadStateC r ch` (pers); `sendable γ sl msgs` (transparent).
- Provisional, other batches': `entryAt p k e` (3h), `beSnap bs γ k` (4a), `dbReader rc γ k` (2e),
  `expiredLeases sl ids` (3c), `mergedSnap mg γ m` (2e's snap message, = 2f's `outSnap`),
  `httpForbidden err` (2e's httptypes).
- Laws: `persistent`, `timeless`, `exclusive`; `histAt_agree`, `histAt_lb` (→ W0's `etcdLb`: K7's
  realization), `histAt_committed`, `histAt_of_committed`, `answered_agree`, `committed_types`
  (only normal and legacy conf-change entries commit), `applyStep_fun`, `histPropose` (a proposer's
  update over `etcdState` → raft's proposal update: 2c's item 4), `isServer_names` (2e's
  `isServer s γ` → `srvNode`/`srvStarted` at `N.etcd = γ`: 2c's item 1), `snapImage_hist`;
  `srvApplied_mono`, `srvApplied_zero`, `srvApplied_hist`, `srvNode_raftNode`, `isRaftNode_node`,
  `rnInit_place`, `applyThread_at`, `applyThread_applied`, `applyc_recv`, `readStateC_recv`,
  `procErr_forbidden`.

`cindex/Api.lean` (`Cindex`): `CIState` (in-memory index, applying index, backend, its stored index),
`isCI ci γ` (pers), `ciState γ m` (excl, client-owned, every method logically atomic), `ciWriter γ`
(excl: the single writer), `ciIface l`; provisional 4a/4b's `beStoredCI be v` (pers), `txStoredCI tx
v` (excl). Laws: `isCI_persistent`, `ciState_timeless`, `ciState_excl`, `ciWriter_excl`,
`beStoredCI_persistent`.

`schedule/Api.lean` (`Schedule`): `isSched sc γ Pay` (transparent bundle of `Schedule`/`Stop`),
`schedOpen γ q` (fractional), `schedTail γ P` (excl: the chain's end), `jobOk`, `funcOk`, `schedCtx`
(transparent); internal `isFifo`, `fifoWorker`, `fifoHead`. Laws: `persistent`, `schedTail_excl`,
`schedOpen_fractional`, `isFifo_isSched`.

## Main changes from the old specs

- **The history is the cluster's** (`histAt` over the committed log, `snapImage` of a snapshot):
  every member's apply thread is at a point of one history; a snapshot install, a restart, a crash
  continue it (K6). This replaces the old ghost logs per incarnation (`ghostOf rp A`, `srvRestR`,
  `kvBatchR`, `dvView`, `epCsAt`), and with them **every R2d'a restart premise**: no window token
  (`srvWinPend`/`winNoMergedSendR`, found false), no `rnWalCommitAbove` (found false), no
  `rnWinInstallAbove`, `rnSnapTermAbove`, `srvRLogLb`, no `σ.b = 0` scope. A restart is a start whose
  `srvRunTok` 2e builds from any durable state (the backend's consistent index may be ahead of the
  WAL's commit: `apply`'s `applyV3` replay, the snapshot's configuration ahead of its index,
  `nonissues/etcd-replay-snapshot-confstate-ahead.md`).
- **Opaque, footprint-sized resources**: `applyThread`/`applyAt` replace the 60-conjunct rows
  (`isServerC`, `srvApplyKVC`, `kvAppliedM`, `srvSnapState`, `srvWTPool`, `rnWalTokA`, `acTok`, ...);
  no auth-mode component, no receipt bound (W0's K7 step budget is the cluster's), no write-token
  pool.
- **Durability is R1's durable node API**: the loop fires `readyEnter` at the WAL's `Save` (2e's
  storage holds `raftState`), the leader sends on `readyCheck` before writing; no WAL ghost of 2d's.
- **The merged snapshot's guard is the code's** (`m.term = raftTerm`, `index ≤ appliedi`), with R1's
  `msgSent_replaceSnap` (needs the term bound: `req/go_etcd_io_raft_v3.md`, from 2d).
- **Lease expiry through `envUpd`** (`revokeExpiredLeases`: `EnvStep.leaseExpire` at the commit, the
  lease live), not a revoke-open premise.
- `cindex`: logically atomic over a client-owned `ciState` with a writer's token (was owned
  `ciIdx`/`ciApplying`); the terms are not modelled (Go stores index and term in two atomics).
- `schedule`: one chain end `schedTail` and a fractional `schedOpen` (was the tracked/untracked
  queue of saved names, `schedStopTok`, `schedPay`, `schedDone`).
- The I/O premises (`walSaveOk`, `walCloseOk`) are 2e's storage handle's (its disk premise), not
  2d's.

## Left out

- `server.go`'s lifecycle (2e's: `Start`, `start`, `GoAttach`, `Cleanup`, `HardStop`, `Stop`,
  `stopWithDelay`, `publishV3` (it proposes through 2c's `raftRequest` from a `GoAttach` goroutine:
  not on the apply path; its update from `envUpd`, `EnvStep.publish`), `adjustTicks`, `purgeFile`,
  `monitor*`, `restoreAlarms`, `CutPeer`/`MendPeer`/`RaftHandler`).
- The request path's public accessors and checks (2c's: `AppliedIndex`, `CommittedIndex`, `Term`,
  `Lead`, `Leader`, `isLeader`, `isActive`, `ensureLeadership`, `ApplyWaitCommit`, `LeaseHandler`).
- `NewUberApplier` (its contract is 3a's: `req/go_etcd_io_etcd_server_v3_etcdserver_apply.md`, from
  2d, item 3); `getTxPostLockInsideApplyHook` (the backend's post-lock hook: its contract is the
  backend's slot (4a), the closure needs the apply thread's `ciWriter`, lent while it holds the
  batch transaction's lock; stated in `applyEntryNormal`'s sketch); `hasMultipleVotingMembers`,
  `raftStatus`, `raftNode.{pauseSending, resumeSending}` (tests), `UpdateConsistentIndexForce` and
  `NewFakeConsistentIndex` (etcdutl and tests), the scheduler's `Pending`/`Scheduled`/`Finished`/
  `WaitFinish` (names only, metrics and tests).

## Open questions for the user

1. **One cluster name** (with 2e, 2c): 2e's handle `isServer s γ` is over W0's opaque `Cluster`;
   2d's vocabulary over `Names` (`.etcd`, `.raft`, `.cfg`), bridged by `isServer_names`. Simpler:
   W0's `Cluster` becomes a structure with the raft names and the configuration (then `Names` goes).
   A W0 change; until then the bridge law.
2. **The apply's configuration** (decided by the coordinator in round 1): every member shares the
   apply-relevant configuration (`Names.mc`, 2e's `ApplyCfg` and `clusterApplyCfg`, fixed at allocation; a `NewServer` premise).
   **Open alternative**: per-member views (each member's own lease minimum TTL,
   `nonissues/etcd-lease-ttl-differs-across-members.md`): the history would record the proposer's
   answer and the other members' replicas relate to it loosely; it needs a member-state relation 3a
   would state, and the proposer's own `mc` in `srvNode`.
3. **Two scope restrictions found in round 1**, each a nonissue with `blocks-proof: yes`:
   `nonissues/etcd-merged-snapshot-same-index-image.md` (a member never saves two merged snapshots of
   one index with different points before installing one: `snapImage`'s source) and
   `nonissues/etcd-concurrent-remove-last-voter.md` (no two `RemoveMember` calls in flight at once:
   an accepted conf change applies in raft). A fork fix would remove each.
4. Nothing else needs a new client-facing premise: no restriction to a first start, one member,
   auth off, no leases, no compaction, or no snapshot.

## Requirement sections written (`## from 2d`)

`req/go_etcd_io_etcd_server_v3_etcdserver.md` (to 2c: answers to its items 1, 4, 6, 8; the wait
registry's predicate, `applyWait`; to 2e: `srvRunTok`, `srvNode`/`srvStarted`, `raftNodeBootCfg`,
`rnCfgOk`, names), `req/go_etcd_io_raft_v3.md` (the term bound for the merged snapshot),
`req/go_etcd_io_etcd_server_v3_etcdserver_apply.md` (3a: `apply.Apply`, `applyStep`,
`NewUberApplier`, `ForceSnapshot`), `req/go_etcd_io_etcd_server_v3_storage_backend.md` (new: 4a/4b:
`beStoredCI`, `txStoredCI`, commits with the index, `Snapshot`), `req/go_etcd_io_etcd_server_v3_storage_mvcc.md`
(3e: `Commit`, `Restore`, the readers' law), `req/go_etcd_io_etcd_server_v3_lease.md` (3c: the expiry
channel under `leaseExpiry`), `req/go_etcd_io_etcd_server_v3_etcdserver_api_rafthttp.md` (new: 2f's
items answered; `Send`, `SendSnapshot`, peers, the received db), `req/go_etcd_io_etcd_server_v3_storage.md`
(new: 2e's WAL storage fires `readyEnter` at `Save`; `SaveSnap`, `Sync`, `Release`, `Close`;
`OpenSnapshotBackend`; hooks), `req/go_etcd_io_etcd_server_v3_etcdserver_api_snap.md` (2e:
`NewMessage`), `req/go_etcd_io_etcd_server_v3_etcdserver_api_membership.md` (new: 2e: validation
deterministic, `shouldApplyV3` writes), `req/go_etcd_io_raft_v3_raftpb.md` (3h: `entryAt`).

## Notes for the coordinator

- `EtcdServer__{Process, ReportUnreachable, ReportSnapshot}.lean` were written by 2d at 09:12:23,
  15 s after 2e wrote `EtcdServer__{CutPeer, RaftHandler}.lean`; if 2e had also written these three,
  2d's write replaced them (2d's generator did not check for existing files then; it does now).
  Please check 2e's report.
- At the start of this batch, `Spec/PkgInit/...bbolt*` imported a missing `Spec.PkgInit.«unsafe»`
  (`etc/gen-specs-pkginit.py`'s `perennial_instances` regex misses `pkg_id.«unsafe»`); it was fixed
  during the batch.

## Round 1 repairs

Reviews: `reviews/2d-provability-1.md`, `reviews/2d-completeness-1.md`. Build: 66 modules OK;
snippets vetted and gofmt-clean; `etc/issues-status.py --check` clean.

Provability:
- **F1** (the coordinator's decision): `Names.mc : ApplyCfg` (2e's type, was 2d's `MemberCfg`), shared by every member, fixed at
  allocation; `histPropose` steps at `γ.mc` (no quantified `mc`); new `applyStep_reach` (the history
  is a `Reach` sequence). Requests to 2e (`NewServer` premise, allocation) and 3a. Per-member views
  recorded as the open alternative.
- **F2**: the cursor `applycPos r k` (exclusive); `applyc_recv` takes it and gives `B.prev = k` and
  `applycPos r B.last`; `srvRunTok_intro` carries it at `p₀.appliedi`; `run`'s chain end tracks it.
- **F3**: R1's `nodeConf` is the `Ready` loop's, lent to the apply thread through a batch with conf
  changes and returned through `notifyc`'s blocking second send; the snapshot's point is
  `snapPoint γ s a` (recorded by the snapshot's maker), and `snapImage_point` gives both threads the
  same `a`: the loop applies R1's `Advance` wand at it, the apply thread opens the image at it.
  Sketches of `raftNode.start`, `applySnapshot`, `applyConfChange`, the header's realization.
- **F4**: `snapImage` is keyed by the snapshot through `snapPoint` (+ `snapPoint_agree`); its source
  is the member's invariant over its snapshot directory, fed by 2f's `recvd`/`dbIn` at `Process`
  (2e's `srvNet`, 2d's `imgAt`). Two images per index cannot be ruled out: Go names the file by index only;
  recorded as `nonissues/etcd-merged-snapshot-same-index-image.md` and an open scope question.
- **F5**: precise request to R1 (`req/go_etcd_io_raft_v3.md`, "from 2d (round 1)": a batch's term
  bound, the start's terms, a sent `MsgSnap`'s non-zero term); `applyBatch_terms`, `msgSnapC_recv`
  (with `m.term ≠ 0`); `applyAll`'s sketch handles `raftTerm = 0` after a restart (the guard fails).
- **F6**: `ReqAppliedRead` replaced by `ReqReadAfterApplyWait` (the store's revision after the wait);
  `nonissues/etcd-applied-index-stale-after-snapshot.md` filed.
- **F7**: laws `isRaftNode_storage`, `nodeSnapLb_stor`, `nodeAdvanced_applied`, `msgSnapC_recv`;
  `ReqDriverLoop` no longer reads the storage after `stop`.
- **F8**: the conf-change waiter's payload (`answered`, `histAt`, `membs` the history's members, `err
  = nil` iff success, `advancedAt`) in `apply.spec`'s sketch and the request to 2c.
- **F9**: `Assumes` of `ReqRestartContinues`, `ReqCrashKeepsAnswered`, `ReqLeaseExpiry`.
- Second tier: S1 (`histPropose` takes raft's namespace `etcdN .@ "raft"`), S2 (non-empty normal
  entries), S3 (the history kept per operation, translated through `committedLb`), S4 (`srvStarted`
  on `applyAll`, `applyEntries`, `apply`, `applyEntryNormal`), S5 (`stopWithDelay` a raw goroutine
  sending on `errorc`), S6 (re-examined: plausible with `StepDownOnRemoval` off, which etcd's
  `raftConfig` leaves; `nonissues/etcd-concurrent-remove-last-voter.md`, scope), S7 (`ciState` in
  one invariant, with an agreement half beside `ciWriter`; the storage request corrected), S8 (the
  state machine is at `ci ≥ appliedi`, always). S9: the lessor's channel carries `leaseExpiry`
  (request to 3c).

Completeness:
- **F1**: the slot `srvReadAt s γ k` with `srvApplied_read`, `srvReadAt_mono`; requested of 3e, 3c,
  3d (none has a read predicate yet: 3e's main `Api.lean` is not written, 3c has `lessorAt`).
- **F2**: `readCtx_register` (with `srvIdSpace`), `readReg_register`, `readReg_get` (`readTicket`).
- **F3**: as provability F8.
- **F4**: `srvMember_node`, `srvNode_agree`, `srvRunTok_intro`, `applyInit` with `applyInit_ep` (`ep` is
  `run`'s), `srvStopped_disk` (with 2e's `srvClosed`, to `memberDisk γ.etcd id ds`); `srvRunTok` and
  `srvStopped` take the directories `ds`; member ids are `Nat` as 2e's (raft's node id `W64 id`).
- **F5**: `srvNode_errorc` (2f's `errChanOk`); `run` returns on `errorc`; `applyEntries`' sketch
  fixed; `stopWithDelay`'s trusted spec requested from 2e; snippet `ReqRemovedSelfStops`.
- **F6**: `Process.spec` takes 2e's `srvNet γ.etcd ν ∗ Rafthttp.recvd ν m` (the received database's `dbIn`);
  `applySnapshot`'s sketch names the source.
- 2f's and 2e's needs: `srvNode` holds from the server literal on (before `tr.Start()`), `procErr` via
  `procErr_forbidden`, `IsIDRemoved` with a thread token (round 0). S1: snippet `ReqReports`. S2: the
  `srvNode` docstring fixed. S3: the simple-token waiter added to `ReqReadAfterApplyWait`'s users and
  to 3d's request. S4: answered in the request to 2e (`0 ≤ heartbeat`, `raftNodeBuilt` = `rnInit`).
  S6: done. S8 (`Backend()` and the swap) and S5, S7, S9 left for round 2 (no spec change needed by a
  current user).
