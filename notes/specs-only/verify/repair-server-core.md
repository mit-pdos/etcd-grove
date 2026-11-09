# Repair: server-core (2026-11-09)

Group `server-core`: `Spec/go_etcd_io/etcd/server/v3/etcdserver/` top level, `etcdserver/{read,
cindex,errors}/`, `Spec/go_etcd_io/etcd/pkg/v3/{wait,idutil,notify,schedule}/`, snippets
`examples/specreq/{etcdserverreq,etcdserverapply,etcdserverboot,cindex,schedule,wait}`.

## Findings

### Sentinel errors (brief item 3; A3-provability F4, cross-cutting)

**Fixed.** `errors/Api.lean`: the pure `srvErrOf err e` and the constant `srvErrVal e` are
unrealizable (fresh `errors.New` pointers). New: `srvErr err e` (persistent IProp, opaque), the
owner's init law gives each global's value with it (`sentinelAt g e := ∃ v, globalAddr g ↦□ v ∗
srvErr v e`; `errors_init` restated). Laws: `srvErr_persistent`, `_ne_nil`, `_fun`, `_inj`, `_leaf`
(also `srvErrMapped e`), `_notCtx`, `_shape`; `srvErrNotMapped` is now a persistent IProp;
`srvIndef`/`srvUnfired` are IProp defs over `srvErr`; `srvErrShape` restated over `srvErr`.
`raftStoppedErr` (a constant) is gone: raft's `ErrStopped`/`ErrProposalDropped` are R1's
`Raft.errIs g err`, with `raftErr_unmapped` and `raftErr_shape` (the latter also covers
`ErrProposalDropped`, A7-completeness F4.3). lease-auth's request: `authErr_srv` (auth's mapped
errors), `leaseErr_srv` (three mapped, `ErrNotPrimary` unmapped with its shape), `bcryptErr_shape`.
Every spec of mine moved from `⌜… srvErrOf …⌝` to `srvErr`; `read/Api`'s `readErr` is over
`srvErr`/`Raft.errIs`; `ApiReq`'s `srvReply`, `applyResult`, `SrvCallTriple`, `readErr_indef`.
The pure `srvErrOf`/`srvErrVal` stay declared, **deprecated** (docstrings say so, no laws), only so
that other groups' files build until they switch (requests below); the coordinator deletes them
after.

### A7-provability

- **F1** (internal requesters: `isServer`, `threadTok`, `srvGate`). **Fixed.** `ApiApply`:
  `srvStarted_isServer` (`srvNode ∗ srvStarted ⊢ isServer s γ.etcd`), `isServer_member`.
  `GoAttach.spec`: the caller keeps its token, the goroutine runs with the fork's fresh one and ends
  with one (see New decisions). `revokeExpiredLeases`, `applyEntryNormal`, `sendMergedSnap` take and
  give back `threadTok`. `LeaseRevoke.spec` takes no `srvGate` (Go reads nothing `Cleanup` closes);
  `Compact.spec` takes a share only when `phys` (A7-completeness F1's fix).
- **F2** (apply thread's `threadTok`; `srvMember` bridges). **Fixed.** `run`, `applyAll`,
  `applySnapshot`, `applyEntries`, `apply`, `applyEntryNormal`, `applyConfChange`, `snapshot`,
  `compactRaftLog`, `snapshotIfNeededAndCompactRaftLog` take and give back `threadTok`; `run`'s is
  `start`'s fork's, the jobs' the scheduler worker's (`Schedule.funcOk`/`jobOk` now lend the
  worker's token: also A7-completeness S4). `srvNode_member` (`srvNode ⊢ srvMember`) and
  `isServer_member`.
- **F3** (`irrOwn` posts false after the header is set). **Fixed.** `raftRequest`,
  `processInternalRaftRequestOnce` post `∃ h, irrOwnH r dq ir h`; `getRequestType` over `irrOwnH r dq
  ir h`.
- **F4** (interface.go specs; `readEnv`). **Fixed.** New specs `EtcdServer.{Done, Stopping,
  LeaderChanged, NextRequestID, RequestTimeout, ApplyWait, LinearizableReadNotify,
  FirstCommitInTermNotify, LeaderChangedNotify}`; `AppliedIndex.spec`'s post now gives
  `srvApplied` of the value. `ReqReadAfterWrite`'s header cites them; its `KV().Rev()` step still
  rests on 3e's `KV.Rev` contract with `srvReadAt_mvcc` (not checked here).
- **F5** (traced contexts vs `reqCtxOk`). **Fixed differently.** `reqCtxOk` keeps its no-trace
  part at the entry methods: `EnsureTrace` keeps a found trace only given `traceEmpty`, which a
  generic caller lacks, so dropping it there would leave the entry points unprovable. New
  `reqCtxSpan ctx` (otel's span only, any trace) with `reqCtxOk_span`; `AuthInfoFromCtx`,
  `raftRequest`, `processInternalRaftRequestOnce` take it; `doSerialize` takes it too.
- **F6** (`readEnv` rows' tokens). **Fixed.** `Logger`, `LeaderChanged`,
  `FirstCommitInTermNotify` rows take and give back `threadTok`; `LinearizableReadLoop` and
  `requestCurrentIndex` take it.
- **F7** (missing helper specs). **Fixed.** `ensureLeadership`, `isLeader`, `Backend`,
  `NewUberApplier` (over a new internal `srvStores s σ`), `stopWithDelay`, `ApplyWaitCommit`.
- **F8** (`histPropose` step budget). **Not fixed**: open decision 5.1 (K7's budget); the slot
  goes in `histPropose`'s input update (or `processInternalRaftRequestOnce`'s pre) once decided.
- **F9, F10**: recorded already; unchanged.
- **F11** (`IsIDRemoved`'s unneeded token). **Fixed**: dropped.

### A7-completeness

- **F1**: as A7-provability F1, plus `publishV3`, `monitorClusterVersions`, `monitorStorageVersion`,
  `monitorKVHash`, `monitorCompactHash`, `monitorDowngrade` take and give back `threadTok`. 3c's
  `ckptOk` R: `srvStarted` gives `isServer` now (lease-auth moved the closure to `Background()`).
- **F2** (compactor's `compactable`). **Partly**: my side is `Compact.spec` without a gate for
  `phys = false`, and the snippet `ReqCompactorInternal` (a child of `Background`, from `start` on).
  The contract `compactable_intro` is server-boot's: request below.
- **F3** (missing specs). **Fixed**: the above, plus `AuthStore` (3d's `authStoreAt`, `srvAuth`),
  `CommittedIndex`, `ClusterVersion` (post: nothing of the version; a reader needs 2e's
  `RaftCluster.Version`, requested), `MemberList` (A8 F1 below), `FeatureEnabled`. 
  `getTxPostLockInsideApplyHook` stays inlined (internal; its contract is 3a's `hooksOk`).
- **F4**: rows 1-2 fixed (tokens; the `ReadState` row's receive takes `£ 1 ∗ £ 1`, as 2d's
  `readStateC_recv`); row 3 fixed by `Raft.errIs` in `readErr` and `raftErr_shape`.
- **F5** (lease expiry's root context). **Fixed** on my side: law `reqPrin_root`; `reqCtxOk` of
  the root context needs 3d's `WithRoot` post to give a value-child at the metadata key: requested.
- **F6** (`ciOk`/`snapSrvOk`/`statusOk`/`authnIdx` intros). **Fixed**: `applyLent s γ` (the
  resource the apply thread lends the uber-applier) and law `applyLent_opts`; `authnIdx` is
  introduced for all names, which is realizable only if 3a reads `authnIdx` as conditional on the
  entry being applied asking `Authenticate(name, tok)`: requested.
- **S1** (notify in membership): server-boot's (request). **S2** ("provisional" in headers):
  fixed (`ApiReq`). **S3** (health checks): unchanged (etcdhttp untranslated). **S4**: fixed
  (schedule).

### A8 (2e top-level parts)

- **provability F3** (`errorc` self-stop closes the backend under in-flight reads). **Recorded as a
  scope** in `run.spec` (decision below); not fixable in the specs without the fork's gate.
- **provability F4** (member ids raft reserves). **Fixed**: `cluster_alloc.spec` premise `m.id ≠ 0 ∧
  isLocalTarget (W64 m.id) = false`; filed `nonissues/etcd-member-id-raft-reserved.md`
  (runtime `MemberAdd`: the same 2^-63 chance, outside the model).
- **completeness F1** (`MemberList`). **Fixed**: `EtcdServer.MemberList.spec` (W0's `memberList
  lin` step, three outcomes, `Membership.membersOwn`); snippet `ReqMemberListAfterAdd`.
- **completeness F5** (getters, `MoveLeader`, `Downgrade`, `PauseSending`/`ResumeSending`).
  **Fixed**: `CommittedIndex`, `Backend`, `Config`, `ClusterVersion`, `MoveLeader` (no model change,
  `srvErrShape`), `Downgrade` (no client-observable step: the downgrade info is not in W0's model),
  `PauseSending`/`ResumeSending` (over `Transport.Pause`/`Resume`; `raftNode.pauseSending` is not
  translated, so no spec of it); `ReqPartition` pauses and resumes; `ReqGetters`.
- **completeness S2** (ready/stop snippet): `ReqReadyOrStop`. **S3** (`InitialCheck`): not done
  (`CorruptionChecker.InitialCheck` is untranslated and has no caller in the specs; embed only).
- Crash restart (provability F1, F2, F9), F5-F8: not in my assignment (the coordinator's list).

### A10-completeness O1 (Restore gate)

**Recorded as a scope** in `applySnapshot.spec` and `run.spec`: no hash during a snapshot install,
until the user decides A8.

### A6-provability F1 (lease handlers' `hdr.fill`)

**Fixed.** `ApiReq`: `replyHdrOwn p b` (a reply whose header is set), `srvHdrReply`,
`replyHdrOwn_replyOwn`, `replyHdrOwn_header` (four lease bodies: `hdrFillable`). `LeaseGrant`,
`LeaseRevoke`, `LeaseTimeToLive`, `LeaseLeases`, `leaseTimeToLive` reply with it. `Alarm` not:
the apply returns `&pb.AlarmResponse{}` (nil header) and `maintenanceServer.Alarm` checks for it
(A6's alarm half is not a finding). Snippet `ReqLeaseReplyHeader`.

### Coordinator-routed requests

- rafthttp / raft-conf-pb: `Process.spec`, `raftNode.Step.spec` take `Raft.msgRecv`; specs of
  `PauseSending`/`ResumeSending`, `ReqPartition` extended; no citation of `vars_init` in my files.
- raft-conf-pb: `createMergedSnapshotMessage` takes `RaftPb.confStateFull`; `ep.confState` is one
  (`ApiApply` realization text).
- raft-core: `snapshot`'s sketch gets `storedLb` by `appliedLb_storedLb`; `raftNode.start` step 6
  passes the Ready's `deliveredLb` to `readyStor_append`; `raftNode.ApplyConfChange` returns
  `confStateFull`; `node.Advance`'s statement is unchanged (`coreIdle` is internal), noted.
- backend-schema: `ApiApply.beSnap` over `Backend.beSnapN γb s I n`; `createMergedSnapshotMessage`'s
  sketch passes the commit's `beHistLb` to `Snapshot`; `NewServer`'s sketch `keyBackend_intro` at
  `m = true`. (`beTurn` of backend locks: no spec of mine calls `Lock*` directly.)
- lease-auth: all five items (errors' laws above; `NewServer`, `AuthInfoFromCtx`, `LeaseRenew`,
  `applySnapshot` sketches; snippet `ReqKeepAliveFollower`).
- client-core: `MemberID`'s users cite `types.ID.String_ptr`/`URLs__*_ptr`; `raftRequest` cites
  `Context.Value.spec`; denials fired at W0's three-view `deniedSince` (`Range`, `checkLease*`).
- server-boot (`repair-server-boot.md`, "Requests to server-core"):
  1. **Crash** (A8-provability F1, F9): `crashScope` is gone; `disk_crash` concludes
     `crashOutOfScope γ ds` (persistent, opaque: the crashed state breaks `confAboveOk` or a
     snapshot batch was interrupted) as a disjunct; it is stated per generation (`L'`, `crashed`,
     `crashRest` over `diskFiles ds = [backendPathOf ds.dataDir]`); `crashGone_intro` (from
     `srvRunning` at the crash) is its producer; `diskIdle_crash` carries an idle disk across;
     the header names the WAL/snapshot crash laws and raft's `confAboveOk` durable invariant in
     `diskState`'s realization. (raft-core's "split" `raftState_crash` is not in the tree yet; the
     realization text cites its two hard-state cases as the current law states them.)
  2. **`diskAcc`** (F2): an invariant-style accessor at `diskN` (`□ ∀ E, ↑diskN ⊆ E -∗ |={E, E ∖
     ↑diskN}=> ∃ k, diskState k ∗ (∀ k', diskState k' ={E ∖ ↑diskN, E}=∗ True)`); `raftNode.start`'s
     sketch fires the WAL's two updates through it.
  3. `cluster_alloc`'s id premise (above); my duplicate nonissue removed in favour of
     `nonissues/etcd-member-id-raft-reserved.md`.
  4. Storage shapes: `beClosable` (4a's `isBackend` with its whole open token) replaces
     `ServerStorage.beOpen` in the three `bootstrapped*.Close` specs (posts `Backend.beFile`);
     `backendBootRes` is now a definition, `Backend.envOk ∗ ⌜quota ≤ 8 GiB ∧ MemoryMlock = false⌝`,
     `backendBootRes_intro` takes the Mlock fact; sketches of `raftNode.start`, `applySnapshot`,
     `bootstrap`, `NewServer` updated (two-update writes, the allocation step, `snapGone`).
  5. cindex's answer for the hook contract: `cindex/Api.lean`'s header ("What cindex gives the
     backend's pre-commit hook": `txStoredCI` as the session's view of `meta`'s two cells,
     `UnsafeSave` writes exactly them, never lowering).
  6. `NewServer`'s sketch allocates `clusterVerInv` for 3c's `clusterOk`; the compactor's
     `compactable c R` at `R := srvStarted s γ id`, `start` passes `□ R` to `Run`.
  7. MemberList, getters, MoveLeader, Downgrade, Pause/ResumeSending (above); `AddMember`/
     `UpdateMember` give `urlsRight` back on a refusal (second tier); the normalization law is W0's
     (request below).
  8. `lock.go`: the name is `"lk"`, the key checked under `"lk/"`; `ReqReadyOrStop`; the crash cases
     of `storage.go`/`snap.go` are not runnable as Go tests (left).

- apply-txn (`repair-apply-txn.md`): `txnChecked_admitted` (ApiReq: `txnChecked t →
  Apply.txnAdmitted t`); `srvStores_kv` (ApiApply: `kvOk`, `kvDelOk`, `kvSt` together, from
  `NewStore`'s post and 4a's `leaseTxHeld_intro`); `NewServer`/`applySnapshot` sketches name
  `NewUberApplier`'s grown premises (`hooksOk`, `authBeCur`, `clusterVerInv`, `beVer`, `lessorSt`'s
  facts); the sentinel encoding (above); the three-view `deniedSince` (client-core item).

## Requests to client-core

1. W0's `urlsRight`: a law `urlsRight γ ss ⊢ urlsRight γ (Types.urlsNorm ss)` (or keying it by
   `urlsNorm`), and W0's `memberAdd`/`memberUpdate` step compared up to `urlsNorm`, so that
   `ClusterServer.MemberAdd` (which builds the member from `types.NewURLs`) meets
   `EtcdServer.AddMember.spec`'s `urlsRight γ urls` at the parsed URLs (A8-completeness F2).

## Requests to grpc-v3rpc

1. Switch from the deprecated pure `EtcdServer.srvErrOf` to `EtcdServer.srvErr` (an IProp):
   - `togRPCError.lean:40-41`: `(∃ e, ⌜srvErrOf err e⌝ ∗ …)` → `(∃ e, srvErr err e ∗ …)`;
     `⌜(∀ e, ¬ srvErrOf err e) ∧ indefMsg m⌝` → `□ (∀ e, srvErr err e -∗ False) ∗ ⌜indefMsg m⌝`.
   - `authMaintenanceServer__requireAuthInfo.lean:38`, `AuthAdmin__requireAuthInfo.lean:38`,
     `authMaintenanceServer__isPermitted.lean:38`, `AuthAdmin__isPermitted.lean:38`:
     `⌜err = GoInterface.nil ∨ ∃ e ∈ L, srvErrOf err e⌝` → `⌜err = GoInterface.nil⌝ ∨ ∃ e, ⌜e ∈ L⌝ ∗
     srvErr err e`.
   - `Api.lean`'s composition text and `toGRPCErrorMap`'s init law: its keys are the values `v`
     with `srvErr v e` (the owners' `sentinelAt`), not `srvErrVal e`. `srvUnfired`/`srvIndef` are
     IProps now (`⌜resp = null⌝ ∗ srvUnfired err`).
2. The lease handlers' `hdr.fill(resp.Header)`: 2c's replies are `srvHdrReply` (`replyHdrOwn`);
   `replyHdrOwn_header` gives the field and a header to fill, and `replyHdrOwn_replyOwn` the reply
   back. `maintenanceServer.Alarm` is fine as is (its `nil` check).
3. `ClusterServer.MemberList`'s sketch: cite `EtcdServer.MemberList.spec` (exists now);
   `maintenanceServer.{Status,MoveLeader,Downgrade}`: cite `EtcdServer.{CommittedIndex,Backend,
   Config,ClusterVersion,MoveLeader,Downgrade}.spec`; the auth handlers: `EtcdServer.AuthStore.spec`.

## Requests to apply-txn

1. `apply/ApiResult.lean:100` `(∃ e, checkErr … = some e ∧ EtcdServer.srvErrOf err e)⌝` → pull the
   error out of the pure part: `∃ e, ⌜checkErr … = some e⌝ ∗ EtcdServer.srvErr err e`;
   `:126` `⌜EtcdServer.srvErrOf err e⌝ ∗ …` → `EtcdServer.srvErr err e ∗ …`.
2. `txn/Api.lean:78-79`'s comment: the sentinels are now `EtcdServer.sentinelAt` (`errors_init`),
   `srvErr_fun`.
3. `apply/Api.lean`: `statusOk`, `snapSrvOk`, `ciOk`, `authnIdx` are introduced by 2d's
   `applyLent_opts` (drop "provisional"); restate `authnIdx R γ name tok`'s meaning as conditional:
   "under `R`, if the entry being applied (whose index `ConsistentIndex()` answers) asks
   `Authenticate(name, tok)`, the cluster issued `tok.idx` to `name`" (what `applierV3backend.
   Authenticate` needs at that entry; an unconditional reading is false for other names).

## Requests to lease-auth

1. `authStore.WithRoot.spec`: in the token disjunct, also `Context.ctxValueAt ctx ctx'
   (mdIncomingKey)` (it is `metadata.NewIncomingContext`), so that `reqCtxOk ctx'` follows from
   4b's/otel's value laws (A7-completeness F5; `reqPrin_root` covers the principal).
2. `leasehttp.TimeToLiveHTTP.spec`: the decoded `LeaseTimeToLiveResponse` has a non-`nil` header
   (the leader's handler sets one), so that 2c's forwarded `LeaseTimeToLive` meets `srvHdrReply`.

## Requests to server-boot

1. `RaftCluster.Version.spec` (a copy of the version or `nil`, read lock, `threadTok`): used by
   `EtcdServer.ClusterVersion.spec`'s proof and 3c's `clusterOk` at `NewServer`.
2. `V3compactor.compactable_intro` (A7-completeness F2): gate the contract on what `start`
   publishes (e.g. `□ R` with `R` giving `isServer`; the compactor runs only from `start`), and
   restrict the context to children of `Background` (`ctxNoIncoming`, `reqCtxOk`), the call to
   `phys = false` (then `EtcdServer.Compact.spec` needs no `srvGate`).
3. Membership's error values (`vErr`, a constant) in the sentinel encoding, and `ErrIDRemoved`,
   `ErrIDNotFound`, `ErrIDExists`, `ErrPeerURLexist`, ... as `EtcdServer.sentinelAt` (the mapped
   ones, `.memberNotFound` twice) in membership's init law.
4. `RaftCluster.SetVersion`'s `versionChanged.Notify()` (A7-completeness S1): a `notifierAt` in
   `SetVersionChangedNotifier.spec` and a `SetVersion` spec.

## Requests to mvcc

1. mvcc's `ErrCompacted`, `ErrFutureRev` in the sentinel encoding: its init law gives
   `EtcdServer.sentinelAt ErrCompacted .compacted ∗ EtcdServer.sentinelAt ErrFutureRev .futureRev`
   (or `errIs` plus a law in `errors/Api` as for lease: say which, I add the tie).

## New decisions

**GoAttach's token shape.** `GoAttach.spec` now lets the caller keep its `threadTok` and runs the
goroutine with the fork's fresh token (which it must give back at its end). The attached
goroutines need a whole token (`Logger`, `Notifier.Receive`, `raftRequest` take one), and the
callers continue (`run` loops; `revokeExpiredLeases` attaches up to 16 at once). The realization
needs the wait group's counter bounded while the goroutine keeps a whole token: Perennial's
leveled `tokJoinL` keeps level 0 in the group and gives the goroutine `threadTokFrom 1`, so either
the reader pools these callees borrow from move to a level ≥ 1 (their specs taking `threadTokFrom
1`), or the group's counter is bounded otherwise. A bounds-plan decision.

**The self-stop (A8-provability F3) and the restore gate (A10 O1) are scope restrictions on the
server's run**, stated in `run.spec`/`applySnapshot.spec`'s text, not in their statements: no
request-path call in flight when `run` stops on `errorc`; no hash during a snapshot install. The
alternatives are the fork's stop gate (Q7) and A8's hashing alternative.

**`reqCtxOk` kept at the entry methods** (A7-provability F5 fixed differently): see F5 above.

## Build

`etc/specs-build.sh --dir` over `etcdserver/{errors,read,cindex}`, `etcdserver` (top level) and
`pkg/v3/{schedule,wait,notify,idutil}`: **OK (218 modules)**, after the last edit. Snippets: `go vet`
clean for `specreq/{etcdserverreq,etcdserverboot,etcdserverapply,cindex,schedule,wait}`. Builds
were blocked for a while by other groups' in-progress files (`client/v3/Api.lean`,
`apply/Api.lean`), since fixed by them.

## Second pass

- grpc-v3rpc, `rsSink_send`'s new premise (no chunk sent so far has a header): met by
  `RangeStream` (only the last chunk, or the count-only one sent alone, sets `Header`, then
  `rangeStream` returns); recorded in its sketch.
- `endsDecoded` (a share of the message with the pure `endsOk`; `endsDecoded_of_canon` at
  `Proto.norm c = c`): `Range`, `Txn`, `RangeStream` sketches updated (no statement change).
- `Proto.norm`-survival laws: none owed. I own no relation over `Proto.Content`: `replyHdrOwn` is
  over 3h's `replyOwn`, and the request messages' relations (`irrOwn`, `chunkModels`, `reqOwn`) are
  3h's or 2a's.
- raft-core, `ApiBoot.lean:130-133`: replaced with the two cases of the split `raftState_crash`
  (a prefix of the batch's entries with the old record, commit between `wcommit` and `D.commit`;
  or all of them with the batch's record, commit between `wcommit` and the batch's).
- Deprecated `srvErrOf`/`srvErrVal`: **deleted** from `errors/Api.lean`. A final grep found them
  only in comments (`apply/ApiResult.lean`, `txn/Api.lean`, v3rpc's `togRPCError`,
  `authMaintenanceServer__*`, `AuthAdmin__*`, `Api.lean`, `auth/Api.lean`), all of which already
  state their errors with `srvErr`.
- lease-auth (`TimeToLiveHTTP`'s `ltlReply`): new law `ltlReply_replyHdr` in `ApiReq.lean`: the
  forwarded `LeaseInternalResponse` with `ltlReply c id` gives an inner reply with
  `replyHdrOwn p (.leaseTimeToLive id ttl gttl ks)`. `leasepb`'s message type is axiomatized in the
  translation, so the field read belongs to the trusted `leaseTimeToLive`, and the law gives the
  inner reply by its address. `leaseTimeToLive`'s sketch uses it. **No law supplies
  `leasePeerURL`**: `leaseTimeToLive` needs `leasePeerURL (u ++ LeaseInternalPrefix)` for each
  peer URL `u` of the leader its membership view returns. Request to lease-auth: a law relating
  it to the cluster's reserved peer URL sets, e.g. `∀ γ ν urls hs, Types.urlsHosts urls = some
  hs → srvNet γ ν ∗ ([∗list] a ∈ hs, Http.protoAt a (Rafthttp.raftProto ν)) ⊢ ⌜∀ u ∈ urls,
  leasePeerURL (u ++ leasehttp.LeaseInternalPrefix)⌝` (the hosts serve etcd's peer handler), or
  keep it a deployment premise and say so in `TimeToLiveHTTP`'s docstring.
- Build: `etc/specs-build.sh --dir` over my directories plus `etcdserver/{apply,txn,api/v3rpc}` and
  `auth` (the deleted declarations' former users): **OK (532 modules)**; `go vet` clean on my six
  snippet packages.
- mvcc's second pass: `errors/Api.lean` gets `mvccErr_srv.spec` (`isPkgInit mvcc ∗ globalAddr g ↦□ v
  ⊢ srvErr v e` for `ErrCompacted`/`.compacted`, `ErrFutureRev`/`.futureRev`; imports `mvcc/Api`)
  and `srvErr_rangeCtx.spec` (`Mvcc.rangeCtxErr err ∗ srvErr err e ⊢ False`).
- server-boot's second pass: `cindex/Api.lean` gets the definitions `metaBktName` and `ciCells`
  (`meta`'s `consistent_index` and `term` keys, as 4a `Cell`s) and the law `txStoredCI_sess.spec`
  (in a hook session `beSess γb q Fp.none S`, `txStoredCI (btIface γb)` is the session's
  `Schema.ciOf` of `meta`, and storing `c'` gives a session at footprint `ciCells` with
  `hookWrites ciCells S S'`); imports 4a's `backend/Api` and `schema/Api`. **The `confState` cell is
  schema's** (`schema.MustUnsafeSaveConfStateToBackend`, written under the same hook by the
  apply thread's conf changes). Request to backend-schema: a `Schema` footprint
  `confStateCells := Fp.key (Bkt.name .metaB) confStateKey` and a law stating that the save writes
  only it, in a session (`hookWrites confStateCells S S'`), so that server-boot's hook footprint is
  `Fp.union ciCells confStateCells`.
- Build (after these): `etc/specs-build.sh --dir` over `etcdserver/{errors,cindex,read}`, the
  `etcdserver` top level, `pkg/v3/{schedule,wait,notify,idutil}` and `etcdserver/{apply,txn}`:
  **OK (340 modules)**.

### Last relay round

- backend-schema's check: `txStoredCI_sess` had the same gap as `confStateSave_hook` (the save's
  `UnsafePut`s need `beCur γb ciCells C`). **Fixed**: the law takes `beCur γb ciCells C` with the
  session and gives back `beCur γb ciCells C'` with the new session.
- server-boot: `applySnapshot`'s sketch keeps `OpenSnapshotBackend`'s returned `Backend.beRevert`
  in the disk's state until the next `SaveDBFrom`'s directory fsync returns `beNoRevert`;
  `bootstrap`'s opener gets the backend file's `Backend.beNoRevert` (4a's `beFile_of`/`beFile_none`);
  `ApiBoot`'s crash section names the revert state in `diskState`'s realization. Sketch and
  realization text only: no statement changed.
- Build: `etc/specs-build.sh --dir` over `etcdserver/{errors,cindex,read}`, the `etcdserver` top
  level and `pkg/v3/{schedule,wait,notify,idutil}`: **OK (218 modules)**.

## Re-review

From `R-A9-apply-txn-lease-auth.md`:
- **N2** (`srvStores_kv`'s `kvDelOk` at unnamed `be`, `rd`): **fixed**. The law now gives 3a's
  whole `lessorSt le kv be σ.leases σ.kv.store` (which carries `kvDelOk kv γl ls.be ls.rd` with
  `ls.be = be`, `ls.rd ≠ nil`, `leasesLive`) at the member's current backend `be`, named by the new
  internal `srvCurBe s be` (the apply thread's half of `s.be`; `bemu`'s invariant holds the other).
  The lessor's field `s.lessor ↦□ le` comes with it. So `NewServer`/`applySnapshot` build
  `NewUberApplier`'s `optsSt` from it.
- **S1** (`authnIdx`'s facts): `applyLent_opts`' docstring now states that `idx` is a non-zero
  `uint64` and `tok` contains no `.` (3d's `GenTokenPrefix`); the conditional reading of
  `authnIdx` carrying these two facts is still requested of 3a.

From `R-A6-grpc-boundary.md`:
- **N2** (`RangeStream` asked for full ownership plus an `endsDecoded` share): **fixed**, also in
  `Range` and `Txn`. The separate `endsDecoded` conjunct is dropped: W0's `rangeReqOwn`/`txnReqOwn`
  already carry `endsOk` of their content (3h's `*ReqOwn_msgAt`), at whatever ownership.
- Second tier: the sketches' `Proto.decodedAt`, `endsDecoded_of_decoded` and
  `endsDecoded_range_intro` are replaced by 3h's `endsOk_canon`/`endsOk_range_intro`.

From `R-A7-server-req-apply.md`:
- **N1** (`revGetter` ≥ 1): `NewServer`'s sketch now cites the store's `Rev` (≥ 1, never lowered),
  which meets `compactable`'s `rev ≠ 0` (server-boot's).
- **N2**: `srvWatchable_mvcc` also gives 3e's persistent `mvccRevTok γs`; `ReqReadAfterWrite` cites
  `readReg_register`/`readReg_get` and the `Rev` token.
- **N3**: `createMergedSnapshotMessage` and `newSnapshotReaderCloser` give the caller's `threadTok`
  back. `createMergedSnapshotMessage` now also takes `srvStarted`, for its `Logger` call under the
  new `srvNode_member`.
- **N4**: `Start.spec`'s post returns `threadTok`.
- **N5** (`srvNode_member` unprovable: `r.transport` is set after `srvNode` holds): **fixed** by
  restating the bridge with `srvStarted`: `srvNode ∗ srvStarted ⊢ srvMember s γ.etcd id`. Its users
  (the apply side, `ensureLeadership`, the read environment) hold `srvStarted`.
- `revokeExpiredLeases`' sketch records the open `WithRoot` tracing gap (§6 F2; requested of
  lease-auth). `togRPCError.lean:6` is grpc-v3rpc's: skipped.
- Build: `etc/specs-build.sh --dir` over my directories: **OK (218 modules)**; `go vet` clean.
