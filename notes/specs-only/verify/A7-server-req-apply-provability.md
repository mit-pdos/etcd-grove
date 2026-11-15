# A7 (server request path and apply side, batches 2c and 2d): provability verification

Reviewer: independent provability agent, 2026-11-09, at `1aa6fc1337` (branch `specs-only`).
Go sources: `/home/ubuntu/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261107170612-a4d2bb1720b9`
(`S/` below), `pkg/v3@…` likewise. I wrote these findings before reading `open-questions.md`.
I then checked that file only to mark which findings are already recorded.

## Verdict per batch

| batch | verdict | first-tier findings |
|---|---|---|
| **2c** request path (`ApiReq`, `v3_server.go`, `errors/`, `read/`, `pkg/{wait,idutil,notify}`) | **FAIL** | F3, F4, F5, F6 (and F1 for the internal requesters) |
| **2d** apply side (`ApiApply`, `server.go` apply side, `raft.go`, `snapshot_merge.go`, `cindex/`, `pkg/schedule`) | **FAIL** | F1, F2 |
| W0's cluster contract K1-K8 from these specs | **FAIL** (K4, K5, K3's read path), **open decision** (K7) | F1, F2, F4, F5, F6; K7 is open question 5.1, plus F8 |

## Counts

- **Specs:** about 150 spec files in the area (etcdserver about 100 of them, `read` 7, `cindex` 8, wait 7,
  idutil 3, notify 3, schedule 8, plus the vocabularies' laws).
  - **In detail** (Go body, callee specs, every step): 38 specs. These are `Range`, `Put`, `Txn`,
    `Compact`, `LeaseGrant`, `LeaseRevoke`, `LeaseRenew`, `raftRequest`,
    `processInternalRaftRequestOnce`, `doSerialize`, `AuthInfoFromCtx`, `Logger`, `GoAttach`, `run`,
    `applyAll`, `applyEntries`, `apply`, `applyEntryNormal`, `applyConfChange`, `applySnapshot`,
    `snapshot`, `compactRaftLog`, `createMergedSnapshotMessage`, `newSnapshotReaderCloser`,
    `sendMergedSnap`, `revokeExpiredLeases`, `Process`, `IsIDRemoved`, the 7 `read/` specs, the
    `raftNode` specs, `cindex` (8), `wait` (7), `idutil` (3), `notify` (3) and `schedule` (8).
  - **By pattern only**: the remaining `SrvCallTriple` wrappers (auth and role methods, `Alarm`,
    `LeaseTimeToLive`, `LeaseLeases`, ...) and the trivial getters and setters (atomics,
    `Lead`, `Term`, ...). Their pattern closes, except where F3 and F5 apply (any wrapper whose Go body
    calls `EnsureTrace` before `raftRequest` or `doSerialize`). This is uncertain per file.
- **Closing:**
  - Of the 38: 27 close, 11 fail (F1 to F6).
  - Of the about 110 by pattern: these close apart from the shared defects above. Not verified line by line.
- **Snippets:** 52 (`etcdserverreq` 16, `etcdserverapply` 17, `wait` 9, `cindex` 3, `schedule` 3, plus
  `idutil`/`notify` counted under `wait`).
  - 47 close under their stated assumptions.
  - 2 do not: `ReqReadAfterWrite` (F4) and `ReqNoSpaceAlarm`'s path through `applyEntryNormal` (F1).
  - 3 are uncertain: `ReqExpiryRevoke`/`ReqLeaseExpiry` (F1), and `ReqReadAfterApplyWait`, which needs
    3e's `KV.Rev.contract` composed with `srvReadAt_mvcc`. I did not check that contract's statement.
- **Laws:** the 2d laws (`ApiApply.lean` §Laws), 2c's (`ApiReq.lean`), `read`, `wait`, `idutil`,
  `notify`, `cindex` and `schedule`. All are plausible from the stated realizations except
  `histPropose` (F8) and `readNew_init`'s premise `readEnv`, which cannot be established (F4, F6).
  None is vacuous.

## First-tier findings

### F1. The apply side's goroutines and internal requests have no `isServer`, `threadTok` or `srvGate`

- **Specs:**
  - `EtcdServer__revokeExpiredLeases.lean`, pre `srvNode ∗ srvStarted ∗ srvLessor ∗ expiredSl ∗ ⌜leaseExpiry⌝`.
  - `EtcdServer__applyEntryNormal.lean`, the `ErrNoSpace` path.
  - `EtcdServer__sendMergedSnap.lean`, pre `srvNode ∗ srvStarted ∗ mergedSnap`.
- **The step that does not close:** each Go body calls `s.GoAttach(...)`
  (`S/etcdserver/server.go:856,880,2019,1889`). `EtcdServer.GoAttach.spec` takes
  `isServer s γ ∗ threadTok`, and no law gives either from `srvNode`/`srvStarted`:
  - `isServer` is introduced only by `start`/`Start`'s post (`EtcdServer__start.lean:45`,
    `EtcdServer__Start.lean:52`);
  - `isServer_names` goes the other way.
- **Inside the goroutines:**
  - `revokeExpiredLeases` calls `s.LeaseRevoke(...)`, whose spec (`EtcdServer__LeaseRevoke.lean`)
    also takes `srvGate s q`. No internal caller holds a share, and the stop takes the gate whole.
  - The `NOSPACE` goroutine calls `raftRequest` (`isServer`, `threadTok`, `authLb γ lo`, `reqCtxOk s.ctx`).
  - `revokeExpiredLeases` starts up to `maxPendingRevokes` goroutines at once. Each needs its own
    `threadTok` for `GoAttach`, and the spec gives none.
- **Who is affected:**
  - K5: lease expiry through `envUpd`.
  - K5: the quota alarm.
  - The merged snapshot (raft's snapshot transfer to a lagging follower).
  - Snippets `etcdserverreq/lease.go` `ReqExpiryRevoke` and `etcdserverapply/apply.go`
    `ReqLeaseExpiry`/`ReqNoSpaceAlarm`.
- **Suggested fix:**
  - A law `srvNode s N id ∗ srvStarted s N id ⊢ isServer s N.etcd` (the realization already makes
    `isServer` "the request path's invariant and the fields `start` sets").
  - A thread-token source for attached goroutines on the apply side. Either `run` takes the forked
    thread's `threadTok` (Perennial's `wp_fork_tok`) and the server's invariant keeps a pool that
    `GoAttach` borrows from, or a variant of `GoAttach` for the apply thread backed by the wait
    group's own tokens.
  - For `srvGate`: either internal variants of `LeaseRevoke`/`raftRequest` without the gate (they
    run under `s.wg`, which `run`'s stop waits for before `Cleanup`), or the attached goroutine
    lends a share.
- **Status:** not recorded. Open question 3.6 is about the gate for in-flight client requests, not
  internal ones.

### F2. The apply thread holds no `threadTok`, yet its callees require one

- **Specs:** every spec of the apply thread: `run`, `applyAll`, `applySnapshot`, `applyEntries`,
  `apply`, `applyEntryNormal`, `applyConfChange`, `snapshot`, `compactRaftLog`. None takes
  `threadTok`, and neither the realizations of `applyThread`/`applyAt`/`srvRunTok` nor `applyInit`'s
  stated content mention one.
- **The step that does not close:**
  1. `s.Logger()` is called by:
     - `run` (`server.go:753`);
     - `applyAll` (`982`, in `VerifyBackendConsistency(s.Backend(), s.Logger(), …)`);
     - `applySnapshot` (`1027`);
     - `applyConfChange` (`2033`, on every call);
     - `snapshot` (`2109,2111`);
     - `compactRaftLog` (`2163`);
     - `sendMergedSnap` (`1877`);
     - `applyEntryNormal` (`2011`).

     `EtcdServer.Logger.spec` (`EtcdServer__Logger.lean`) takes `srvMember s γ id ∗ threadTok` (the
     reader slot of `lgMu`).
  2. `applyAll` calls `createMergedSnapshotMessage`, whose spec takes `threadTok`.
  3. `createMergedSnapshotMessage` calls `newSnapshotReaderCloser`, whose spec takes `threadTok`.
- **Secondary gap:** `srvMember` itself has no source from `srvNode` (on the apply side) or from
  `isServer` (on the request path: `Range` calls `s.Logger()` in `EnsureTrace`). The only bridge is
  `srvMember_node`, which goes `srvMember → srvNode`.
- **Who is affected:** every apply batch, hence K4 (writes answered), K6 and every snippet in
  `etcdserverapply/`.
- **Suggested fix:**
  - `run.spec` takes `threadTok` (the token `start`'s `go s.run()` gets from `wp_fork_tok`).
  - `applyThread`'s realization owns it, or the apply-side specs thread it explicitly. The
    scheduler's chain (`schedTail`) can carry it inside `applyThread`.
  - Add `srvNode s N id ⊢ srvMember s N.etcd id` and `isServer s γ ⊢ ∃ id, srvMember s γ id`.
- **Status:** not recorded.

### F3. `processInternalRaftRequestOnce`, `raftRequest` and `getRequestType` give back `irrOwn r dq ir` (header unset), which is false after the call

- **The post is false of the code.** `S/etcdserver/v3_server.go:1066-1077` writes `r.Header =
  &pb.RequestHeader{…}` and then its `Username`/`AuthRevision`. The posts return
  `irrOwn r dq ir = irrOwnH r dq ir none`, which at `dq = 1` is `msgAt … c` with
  `irrHeaderHolds c none` (`etcdserverpb/Api.lean:700,721`). 3h's own law `irrOwn_setHeader` turns
  it into `irrOwnH … (some h)`, and no law sets it back.
- **A second step does not close either:** `getRequestType(r)` is called after the header is set
  (`v3_server.go:1084`), but its pre is `irrOwn r dq ir`.
- **Specs:** `EtcdServer__processInternalRaftRequestOnce.lean:80`, `EtcdServer__raftRequest.lean:54`,
  `getRequestType.lean:36`.
- **Callers:** they use only `irrOwn_unwrap`, which takes any header. So the fix costs nothing.
- **Suggested fix:** post `∃ h, irrOwnH r dq ir h`, and `getRequestType` over `irrOwnH r dq ir h`.

### F4. `interface.go` has no specs, so `readEnv` cannot be established and `ReqReadAfterWrite` does not close

- **Missing specs:** `EtcdServer.ApplyWait`, `Done`, `LeaderChanged`, `NextRequestID`, `RequestTimeout`,
  `Stopping`, `LinearizableReadNotify` (`S/etcdserver/interface.go:22-48`) and
  `FirstCommitInTermNotify`/`LeaderChangedNotify` (`server.go:1738,1746`) have no spec in this tree.
  The old tree had all of them (`specs-ref/…/etcdserver/EtcdServer__{ApplyWait,Done,LeaderChanged,
  NextRequestID,RequestTimeout,Stopping,LinearizableReadNotify,FirstCommitInTermNotify}.lean`).
- **Why it matters:** `read.readNew_init.spec` needs `readEnv srv rf …`, which is exactly these
  methods' triples. The read path's whole guarantee (K3/K4 for linearizable reads, `Range.spec`'s
  proof) depends on someone proving `readEnv` at `start`, and there are no callee specs to prove it from.
- **The snippet:** `etcdserverreq/read.go` `ReqReadAfterWrite` calls `s.LinearizableReadNotify(ctx)`.
  Its header admits the spec is "not yet written", and it also needs a law relating `KV().Rev()` to
  `srvApplied` (3e's `KV.Rev.contract` with `srvReadAt_mvcc` might give it; not checked).
- **Suggested fix:** restore the eight specs (2c's or 2e's). `LinearizableReadNotify` should be stated
  as `Read.LinearizableReadNotify.spec` at `isServer`'s `readAt s.read γ.raft (srvApplied s γ)`.
- **Status:** not recorded (a coverage gap; it also belongs in A7's completeness report).

### F5. Traced contexts cannot satisfy `reqCtxOk`: `Txn` (writes), `Compact` and `doSerialize` do not close

- **The conflict:**
  - `reqCtxOk ctx := ctxTraceIs ctx none ∗ ctxSpanOk ctx` (`ApiReq.lean:351`).
  - `EnsureTrace`'s post gives `ctxTraceIs ctx' (some t)` (`traceutil/EnsureTrace.lean`).
  - `ctxTraceIs_agree` makes the two incompatible. A `WithValue` at another key keeps the trace
    (`ctxTraceIs_value`).
- **The steps that do not close:**
  - `Txn`, the write path (`v3_server.go:338,374-375`): `EnsureTrace`, then `WithValue(StartTimeKey)`,
    then `raftRequest(ctx, …)`, whose pre needs `reqCtxOk ctx`.
  - `Compact` (`v3_server.go:390-391`): `EnsureTrace`, then
    `processInternalRaftRequestOnce(ctx, …)`, whose pre needs `reqCtxOk ctx`.
  - `doSerialize` (called by `Range`, a read-only `Txn`, `RangeStream`, after their `EnsureTrace`):
    it holds `ctxTrace ctx` but calls `s.AuthInfoFromCtx(ctx)`, whose pre needs `reqCtxOk ctx`.
- **What the callees actually read:**
  - `AuthInfoFromCtx` (`v3_server.go:1206-1216`) reads no trace.
  - `processInternalRaftRequestOnce` reads only `trace.SpanFromContext` (otel).
  - `raftRequest` reads `ctx.Value(StartTimeKey{})` with a checked assertion.
- **Who is affected:** every write transaction, `Compact`, and every read's permission check. That is
  K4 for most requests (Kubernetes' CAS, `txnlin`, the compactors).
- **Suggested fix:** take only `OtelTrace.ctxSpanOk ctx` (plus `∃ o, ctxTraceIs ctx o` if needed) in
  `AuthInfoFromCtx`, `processInternalRaftRequestOnce` and `raftRequest`. Keep `reqCtxOk` only at the
  methods that call `EnsureTrace` on a fresh context.
- **Status:** not recorded.

### F6. `readEnv`'s `Logger`, `LeaderChanged` and `FirstCommitInTermNotify` triples take no `threadTok`, but their implementations need one

- **Spec:** `read/Api.lean` `readEnv`: `{{ True }} srv.Logger() {{ isLogger }}`, and likewise
  `LeaderChanged()` and `FirstCommitInTermNotify()`.
- **Why they cannot be proved:**
  - `LeaderChanged` and `FirstCommitInTermNotify` are `Notifier.Receive()` (`pkg/notify/notify.go`:
    `RLock`), whose spec takes `threadTok` (`notify/Notifier__Receive.lean`).
  - `Logger` is `EtcdServer.Logger.spec` (`threadTok`, `srvMember`).
  - So the triples cannot be proved from their callee specs (F4 aside).
- **A related gap in the loop:** `Read.LinearizableReadLoop.spec` (pre `readLoopTok r` only) and
  `requestCurrentIndex.spec` call those methods. The loop runs under `GoAttach`, which gives it a
  `threadTok`, but the specs do not take it.
- **Suggested fix:** those three triples take and return `threadTok`, and `LinearizableReadLoop` and
  `requestCurrentIndex` take `threadTok`.
- **Status:** not recorded.

## Second-tier findings

- **F7. Callee specs the sketches cite but that do not exist:**
  - `ensureLeadership` (`revokeExpiredLeases`: "2c's");
  - `isLeader` (`applyEntryNormal`);
  - `Backend` (`applyAll`);
  - `NewUberApplier` (`applySnapshot`);
  - `stopWithDelay` (`applyEntries`, a `go` statement);
  - `ApplyWaitCommit` (`waitAppliedIndex`).

  The old tree had the first four. As internal helpers they can be inlined, but the sketches name
  them as specs (`ensureLeadership` calls `s.read.LinearizableReadNotify` and `Logger`, so inlining
  meets F2/F6).
- **F8. `histPropose.spec` has no slot for K7's step budget.** The cluster's invariant cannot keep
  `etcdState_revFits`/`sizeFits` (W0's `State.lean:109,142`) through commits it cannot refuse unless
  every proposal pays in advance. `histPropose`'s input update carries no receipt (`ApiApply.lean:532`),
  and no other proposal path exists. Whatever open question 5.1 decides, `histPropose` (or
  `processInternalRaftRequestOnce`'s pre) must take the per-entry budget, proportional to the entry's
  events for `sizeFits`. **Recorded as an open decision** (5.1); the `histPropose` consequence is not.
- **F9. `Generator.Next.spec` is an assumed contract on etcd's own code, false across runs**
  (`idutil/Api.lean` header). This is **recorded**: open question 5.x line 329,
  `nonissues/etcd-request-id-restart-reuse.md`.
- **F10. `snapImage` holds only if no two merged snapshots share an index:** **recorded** (F9 of
  `open-questions.md`, line 382).
- **F11. `EtcdServer.IsIDRemoved.spec` takes `threadTok`, but its body
  (`RaftCluster.IsIDRemoved.spec`) needs none.** This is an unneeded premise (harmless: `Process`
  holds one).

## Proof plans that close (summary)

- **`processInternalRaftRequestOnce`** (modulo F3 and F5):
  1. The atomics, then `exceedsRequestLimit` (outcome 2).
  2. `Next` gives `idFresh`, then `AuthInfoFromCtx` (`reqPrin`: `p`, or `tls` with auth off).
  3. `Marshal` (`irr_content`, depth from `irrWf`), then the size check (outcome 2).
  4. `waitToks_take` (`idFresh_excl` gives `id ∉ U`), then `Register`.
  5. `histPropose` at `srvCfg`, with `D := (· = data)`, `γ.raft.dup = false` (`srvNode_raftNames`),
     then `raftNode.Propose`. The derived update fires the caller's `srvStep` update when
     `Apply.irrStep_step` gives a fired answer, and otherwise aborts it into the waiter's deposit
     (`irrStep_oldRev`: no change).
  6. `select`. On `ch`, `waitRecv_recv` gives `applyResult`. On `cctx.Done`, `Trigger` with
     `waitRecv` (outcome 3). On `s.done`, outcome 3.

  `srvStep`'s `tls` disjunct covers a header filled with auth off, since `Req.isRead` is false for
  every raft-proposed request (`Model.lean:818`; read-only transactions take the read path,
  `v3_server.go:345`).
- **`Range`** (modulo F5 and F2's `srvMember`):
  1. `readReg_register` gives `readTicket` and `committedLb l0`.
  2. `Read.LinearizableReadNotify` at `l0` gives `committedLb l ∗ srvApplied |l|` with
     `opsOf l0 <+: opsOf l`.
  3. `srvApplied_read`, then `srvReadAt_auth`/`_mvcc` with `srvReader_mvcc`, then `doSerialize`.
  4. `readReg_get` at `(kr, res)`.

  The registration is linearizable: the read point `kr ≥ |l| ≥ |l0|` is a state the cluster
  passed through after the call began.
- **The read loop** (modulo F6):
  1. Swap the notifier under `mux.Lock`.
  2. Register fresh contexts at the deposited bound (`readEnv`'s registration, ApiApply's
     `readCtx_register`).
  3. `readState_registered` and `readState_fire` give `l'` with `|l'| = i`, then
     `ApplyWait(i)` / `AppliedIndex ≥ i` (downward closure of `A`).
  4. `notify(nil)`.

  Stale read states are filtered by the local `requestIDs`.
- **`apply` / `applyEntryNormal` / `applyConfChange`** (modulo F1, F2):
  - `SetConsistentApplyingIndex` when `ci < k`.
  - `Apply.Apply` with `IsRegistered` (`waitWasReg` for own ids; `waitToks_never` for others, from
    the invariant's map of issued ids).
  - `Trigger(id, ar)` with `P id ar` from `answered`.
  - The deferred `SetConsistentIndex(k)`.
  - The conf change's `Trigger` with `advancedAt`.
- **`applyAll`** (modulo F2):
  - `applySnapshot` and `applyEntries`.
  - `applyWait.Trigger(appliedi)` with `□ srvApplied` (`applyThread_applied`).
  - `<-notifyc`, then `<-raftAdvancedC` (`nodeAdvanced`), or `stopping` (`return`, post at
    `B.last`).
  - `snapshotIfNeededAndCompactRaftLog`.
  - The `msgSnapC` arm. The guard `m.term = raftTerm ≠ 0` with `applyBatch_terms` gives
    `appliedt ≤ m.term`; `sn.index ≤ appliedi` comes from the guard.
- **`cindex`:**
  - The `ConsistentIndex` load with `idx = 0 → stored ≠ none` excludes the nil backend's `ReadTx`.
  - `UnsafeSave`'s `c ≤ idx` excludes `verifyConsistentIndexIsLatest`'s panic.
- **`wait`, `notify`, `idutil`, `schedule`:** every spec closes from its realization. Each of the
  snippets (`ReqRegisterTrigger`, `ReqGiveUp`, `ReqWaitTime`, `ReqIsRegistered`,
  `ReqNotifyAfterReceive`, `ReqNotifyConcurrent`, `ReqIdsDistinct`, and the schedule chain and stop)
  closes with the caller's choice of `P`.

## The cluster contract (K1-K8) from these specs

| item | owner | status here |
|---|---|---|
| K1, K2, K8 | 2e | not this area |
| K3 | 2e/2a, over 2c | needs `readEnv` at `start`, which F4 and F6 block |
| K4 | 2c | at-most-once holds by construction (`idFresh`, one `Propose`, `dup = false`, `irrBackOk` for stale tokens), and the read registry gives the read clause; but F5 blocks `Txn`, `Compact` and every permission check, and F3's post is false |
| K5 | 2c/2d | lease expiry and the quota alarm are blocked by F1; publication goes through `publishV3` over `isServer` and closes |
| K6 | 2d | `histAt` is indexed by the committed log and continued by snapshot and restart (`snapImage_point`, `srvRunTok_intro`); the plan closes modulo F2 and F10 |
| K7 | 2c/2d | `histAt_lb` realizes `etcdLb`; `revFits`/`sizeFits` are open decision 5.1, plus F8 |

## Targets ranked by need of revision

1. `ApiReq.lean` `reqCtxOk` use in `AuthInfoFromCtx`, `processInternalRaftRequestOnce` and `raftRequest` (F5).
2. The apply thread's resources: `run`, `applyThread`, `Logger`, `srvMember` bridges (F2).
3. `revokeExpiredLeases`, `applyEntryNormal`, `sendMergedSnap` and `GoAttach`'s sources (F1).
4. `read/Api.lean` `readEnv`, `LinearizableReadLoop` and `requestCurrentIndex` (F6), and the missing
   `interface.go` specs (F4).
5. The `irrOwn` posts (F3).
6. `histPropose` and the K7 budget (F8, open 5.1); the missing helper specs (F7).
7. `cindex`, `wait`, `notify`, `idutil`, `schedule`: no change needed.

No new bug in the Go code was found. The idutil reuse across runs and the merged-snapshot image are
already in `nonissues/`.
