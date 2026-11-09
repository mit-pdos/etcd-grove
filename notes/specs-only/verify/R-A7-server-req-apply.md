# R-A7: re-review of the server request path (2c) and apply thread / raft node (2d)

Reviewer: independent re-review (`reverify-brief.md`), 2026-11-09, at `974e05095b` (branch `specs-only`),
diffed against `1aa6fc1337`. Read-only apart from this file. Go: `.lake/src/server` (`S/` below).
I wrote my verdicts on each original finding before I read `repair-server-core.md` and
`open-questions.md`. I read them afterwards only to check disagreements and to mark recorded decisions.

Scope:
- the top-level files of `Spec/go_etcd_io/etcd/server/v3/etcdserver/` (`EtcdServer__*`, `raftNode__*`,
  `ApiReq`, `ApiApply`, `ApiBoot`);
- `etcdserver/{read,cindex,errors}/`;
- `pkg/v3/{wait,idutil,notify,schedule}/`;
- the snippets in `examples/specreq/{etcdserverreq,etcdserverapply,etcdserverboot,cindex,schedule,wait}`.

## Verdicts

| batch | verdict | new first-tier |
|---|---|---|
| **2c**: request path (`ApiReq`, `v3_server.go`), `read/`, `errors/`, `pkg/{wait,idutil,notify}` | **FAIL** (narrowly) | N1 (a 2c user is not served: the compactor's contract asks for `rev = 0`), N2 (no `Rev` right for `KV().Rev()`: the recorded `ReqReadAfterWrite` gap, made precise) |
| **2d**: apply side (`ApiApply`, `server.go` apply side, `raft.go`, `snapshot_merge.go`), `cindex/`, `pkg/schedule` | **FAIL** | N3 (`createMergedSnapshotMessage` consumes the apply thread's `threadTok`), N5 (`srvNode_member` cannot be realized) |
| the boot files in my scope (`ApiBoot`, `EtcdServer__Start`, `etcdserverboot` snippets) | **FAIL** | N4 (`Start` consumes the caller's only `threadTok`; `ReqStartThree` and `ReqRestart` do not close) |

Open decisions that also apply here (recorded; each still counts):
- 5.1: `histPropose`'s step budget.
- C45: `GoAttach`'s token shape.
- C46: the `errorc` self-stop and the restore gate.
- C47: `reqCtxOk` stays at the entry methods.
- §6 F2: `WithRoot`'s `rootTokOk`. The default simple-token provider does not give it, so
  `revokeExpiredLeases` with auth on and simple tokens has no usable `WithRoot` spec. That sketch
  does not mention it.

All six snippet packages are `go vet`-clean.

## The original first-tier findings

### A7-provability

| # | finding | status | evidence at `HEAD` |
|---|---|---|---|
| F1 | internal requesters lack `isServer`/`threadTok`/`srvGate` | **resolved** | See [F1 detail](#f1-detail). The token-pool question is open decision C45. |
| F2 | apply thread holds no `threadTok`; `srvMember` has no source | **partly resolved** | The token is threaded through the apply chain: `run`, `applyAll`, `applySnapshot`, `applyEntries`, `apply`, `applyEntryNormal`, `applyConfChange`, `snapshot`, `compactRaftLog`, `snapshotIfNeeded…`. `Schedule.funcOk`/`jobOk` lend the worker's token, and `NewFIFOScheduler` forks the worker with `wp_fork_tok_body` (that lemma exists: `Perennial/GooseLang/Lifting.lean:1993`). On the request path, `isServer_member` gives `srvMember`. **But** on the apply side the new bridge `srvNode_member` cannot be realized (**N5**), and `createMergedSnapshotMessage` eats the token (**N3**). |
| F3 | `irrOwn` post false after the header write | **resolved** | Posts are now `∃ h, irrOwnH r dq ir h`: `processInternalRaftRequestOnce.lean`, `raftRequest.lean`. `getRequestType` is over `irrOwnH r dq ir h`. This matches `v3_server.go:1066-1077`. |
| F4 | `interface.go` methods unspecified; `readEnv` unprovable; `ReqReadAfterWrite` | **resolved, except a recorded gap** | All of `ApplyWait`, `Done`, `Stopping`, `LeaderChanged`, `FirstCommitInTermNotify`, `LeaderChangedNotify`, `NextRequestID`, `RequestTimeout`, `LinearizableReadNotify` and `ApplyWaitCommit` now have specs. Each `readEnv` row follows from them. `ReqReadAfterWrite` is still open: the recorded gap "`KV().Rev()` step, not checked". Its missing piece is concrete (**N2**). |
| F5 | traced contexts cannot meet `reqCtxOk` | **resolved** (C47) | `reqCtxSpan` (otel span only) and `reqCtxOk_span` are in place. `AuthInfoFromCtx`, `doSerialize`, `raftRequest` and `processInternalRaftRequestOnce` take `reqCtxSpan`. `EnsureTrace`'s post gives `ctxValueAt … traceKey`, and otel's `ctxSpanOk_value` carries the span across it. |
| F6 | `readEnv`'s `Logger`/`LeaderChanged`/`FirstCommitInTermNotify` rows lack `threadTok` | **resolved** | Those rows, `LinearizableReadLoop` and `requestCurrentIndex` now take and give back `threadTok`. |
| F7 | cited helper specs missing | **resolved** | `ensureLeadership`, `isLeader`, `Backend`, `NewUberApplier`, `stopWithDelay` and `ApplyWaitCommit` exist. |
| F8 | `histPropose` has no K7 budget | **open decision** 5.1 | Recorded: "Gaps left open". |
| F9, F10 | idutil reuse across runs; merged-snapshot image | **recorded** (as before) | |
| F11 | `IsIDRemoved` takes an unneeded `threadTok` | **resolved** | The premise is gone. |

<a id="f1-detail"></a>**F1 detail (evidence at `HEAD`).**
- `srvStarted_isServer` (`ApiApply.lean:621`) supplies `isServer`.
- These specs take and give back `threadTok`: `revokeExpiredLeases`, `applyEntryNormal`,
  `sendMergedSnap`, `publishV3`, `monitor*`.
- `GoAttach` hands the goroutine a fresh token and returns the caller's.
- `LeaseRevoke.spec` has no `srvGate`. Go's `LeaseRevoke` is `requireAuthInfo` + `raftRequest`
  (`v3_server.go:470-486`). `run` runs `s.wg.Wait()` before `Cleanup`, so no attached goroutine
  outlives the backend.

### A7-completeness

| # | finding | status | evidence at `HEAD` |
|---|---|---|---|
| F1 | internal requesters cannot meet 2c's pres | **resolved** | As provability F1. In addition, 3c's `ckptOk` is at `R := srvStarted s γ id` (`NewServer.lean:104`), and `Compact` takes a gate only when `phys`. |
| F2 | compactor's `compactable` vs `Compact.spec` | **partly resolved** | `compactable c R` is gated on `R := srvStarted`. The context is a child of `Background`, the request is non-physical, and there is no gate. **But** the contract quantifies over every `rev : Int`, while `Compact.spec` needs `rev ≠ 0` (**N1**). |
| F3 | missing accessor/check specs | **resolved** | `ensureLeadership`, `isLeader`, `LinearizableReadNotify`, `AuthStore`, `Backend`, `CommittedIndex`, `ClusterVersion`, `MemberList`, `FeatureEnabled`, `NewUberApplier`, `Config`, `MoveLeader` and `Downgrade` exist. Only two old files have no counterpart: `getTxPostLockInsideApplyHook` (proved once inside `NewUberApplier`'s sketch) and `checkMembershipOperationPermission` (inlined in the trusted member methods). The test-only `read.newNotifier`/`notify` are dropped, as before. |
| F4 | `readEnv` rows vs `Notifier.Receive`, `readStateC_recv`, `raftStoppedErr` | **resolved** | Row 1 takes `threadTok`. Row 2's `ReadState` receive now takes `£ 1 ∗ £ 1`, which matches `readStateC_recv` (`ApiApply.lean:889`). Row 3's errors are `readErr ∋ Raft.errIs ErrStopped`, which matches R1's `nodeErr` (`raft/v3/Api.lean:467`). `raftErr_unmapped`/`raftErr_shape` cover `ErrProposalDropped`. |
| F5 | `WithRoot` context has no `reqPrin`/`reqCtxOk` | **resolved** | `reqPrin_root` (`ApiReq.lean:330`) is in place. 3d's `WithRoot` post now gives `ctxValueAt ctx ctx' mdIncomingKey`, so `reqCtxOk` follows from `ctxTraceIs_value`/`ctxSpanOk_value`. That still needs `reqCtxOk s.ctx`, which only `srvStarted`'s realization ("`s.ctx`") holds. See second tier. |
| F6 | `ciOk`/`authnIdx`/`snapSrvOk`/`statusOk` have no introduction | **resolved** | `applyLent_opts` (`ApiApply.lean:639`). The conditional reading of `authnIdx` is requested of 3a. |
| S1 | notifier in membership | **resolved** | `RaftCluster.SetVersion.spec` is new. |
| S4 | scheduler worker's token | **resolved** | Forked with `wp_fork_tok_body` and lent to each job. |

## The sentinel encoding (`srvErr`/`sentinelAt`)

I checked it against `S/etcdserver/api/v3rpc/util.go:35-100` and `S/etcdserver/errors/errors.go:22-45`.

- **`srvErrOf` and `srvErrVal` are gone from every Lean statement and every snippet.** Only prose
  mentions remain:
  - `errors/Api.lean:43` ("Removed");
  - `apply/ApiResult.lean:98`;
  - `txn/Api.lean:83`;
  - in A6's area, `v3rpc/togRPCError.lean:6`, whose sketch still says "the server errors `srvErrOf`
    names" (stale wording only).
- **`raftStoppedErr` is gone.** `readErr` uses `Raft.errIs ErrStopped`.
- **`errors_init` matches `toGRPCErrorMap` exactly.** It lists the 20 `etcdserver/errors` keys. It
  omits `ErrUnknownMethod` and `ErrTimeoutLeaderTransfer`, which are unmapped, and the omission is
  correct.
- **`srvErrMapped` is the map's key set.**
- **`srvErr_inj`'s exception is right.** The only `EtcdErr` with two keys is `.memberNotFound`
  (`ErrIDRemoved`, `ErrIDNotFound`). `.canceled` has a second key, `context.Canceled`, but
  `srvErr_notCtx` excludes context errors.
- **The other laws are plausible.** `srvErr_fun`, `srvErr_notCtx` and `srvErr_rangeCtx` follow from
  the realization (distinct `errors.New` cells).
- **None of the laws is vacuous.**
- **The derived predicates now use `srvErr` correctly.** These are `srvIndef`, `srvUnfired` and
  `srvErrShape`. On the reply side they are `srvReply`, `applyResult`, `raftRequest`'s `.err e`
  arm and `doSerialize`'s `.invalidAuthToken`/`.authOldRevision`.
- **`readErr_indef` closes.** It uses `srvErr_fun` with the three server sentinels' kinds,
  `raftErr_unmapped`, and `srvErr_notCtx`.
- Second tier:
  - `readErr_shape` has no `isPkgInit raft` premise, but `raftErr_shape` needs one. It closes only
    if `Raft.errIs`'s realization carries the package's initialization (uncertain).
  - `version`'s three mapped errors (`ErrInvalidDowngradeTargetVersion`, …) have no owner law. Only
    the trusted `Downgrade.spec` returns them, and only with `srvErrShape`.

## New first-tier findings

### N1. `compactable_intro` asks for `Compact` at `rev = 0`, which `Compact.spec` excludes

- **The mismatch.** `V3compactor.compactable_intro` (`api/v3compactor/Api.lean:129-135`) asks for a WP
  of `Compact` for every `rev : Int`. `NewServer` proves it "from 2c's `EtcdServer.Compact.spec`"
  (`NewServer.lean:106`). But `Compact.spec` takes `⌜rev ≠ W64 0⌝`, a needed scope premise
  (`issues/etcd-restore-scheduled-compact-zero.md`). At `rev = 0` there is no spec to prove the WP
  from, so the compactor's contract cannot be introduced.
- **The compactors do meet it in Go:**
  - `revision.go:82` skips `rev <= 0`;
  - `periodic.go:126` skips `rev == lastRevision`, and `lastRevision` starts at `0`.
- **But periodic's proof cannot show it from today's `revGetter`.** That contract says "any
  `int64`". After a success `lastRevision ≠ 0`, so a later `Rev() = 0` would be compacted.
- **Who is affected:** the auto-compactor (U6 of the completeness report). The snippet
  `ReqCompactorInternal` assumes `rev ≥ 1` and so hides the gap.
- **Fix:**
  - add `⌜rev ≠ 0⌝` to `compactable_intro`'s WP and to `compactable`'s meaning;
  - have `revGetter` say `Rev()` returns at least 1 (3e's store starts at revision 1), or have the
    periodic loop's sketch derive `rev ≠ 0` from its own guards;
  - also fix `compactable_intro`'s comment, which still says "gate share from `R`".
  - These edits are in A8's files; the requirement is 2c's.

### N2. No `Rev` right reaches the request path's clients; `ReqReadAfterWrite` does not close

- **The missing resource.** `ReqReadAfterWrite` (`etcdserverreq/read.go:23`) calls `s.KV().Rev()`.
  `EtcdServer.KV.spec` gives `srvWatchable s γ w`, and `srvWatchable_mvcc` gives
  `Mvcc.watchableAt w γs` (hence `isMvcc`). 3e's `KV.Rev.contract` (`mvcc/Api.lean:342`) also takes
  `revRd γ rt`, which is `mvccReaders γ 1` or `mvccRevTok γ ∗ threadTok`.
  - `NewServer` takes the persistent `mvccRevTok` for good (`NewServer.lean:86-88`).
  - No law of `ApiReq`, `ApiApply` or `ApiBoot` exports it, and `srvGate`'s reader tokens are not
    exported either.
- **The read point is a second step without a cited source.** The snippet needs the put's commit
  ordered before the read's registration. It can get that from `readReg_register`/`readReg_get`:
  - register a `□ AU` whose `Q` is `⌜Reach σput σ⌝`, using `etcdLb_reach` with the put's `etcdLb`;
  - take its `committedLb l0` to `EtcdServer.LinearizableReadNotify`;
  - at `Rev`'s commit, apply `readReg_get` at `srvReadAt_mvcc`'s `histAt γ k' σ`.

  The header cites none of these laws.
- **Who else is affected:** 2a's `header.fill`/`fillWithoutRevision` (`KV().Rev()`) need the same
  right. A6 should note it: `header.fill.spec` also takes no `threadTok`.
- **Status:** recorded only as "not checked" ("Gaps left open": `ReqReadAfterWrite`'s `KV().Rev()`).
- **Fix:**
  - `srvWatchable_mvcc : srvWatchable s γ w ⊢ ∃ γs, watchableAt w γs ∗ mvccRevTok γs` (the
    server's realization holds the persistent token);
  - cite `readReg_register`, `readReg_get`, `etcdLb_reach` and `srvReadAt_mvcc` in the snippet's
    header.

### N3. `createMergedSnapshotMessage` (and `newSnapshotReaderCloser`) consume the apply thread's `threadTok`

- **The leak.**
  - `createMergedSnapshotMessage.spec` takes `threadTok`, and its post (`applyThread ∗ mergedSnap`)
    does not return it.
  - `newSnapshotReaderCloser.spec` takes `threadTok` and returns only `dbReader rc γ k`.
- **Why `applyAll` no longer closes.** `applyAll` calls them on the `msgSnapC` arm
  (`server.go:1011-1013`), then calls `sendMergedSnap`, whose spec now takes `threadTok`, and must
  return `threadTok`, which it now does for `Schedule.funcOk`. So `applyAll.spec` fails on the
  merged-snapshot path.
  - This was pre-existing, but it is now a break. The repair made `applyAll` give the token back
    and made `sendMergedSnap` take one, while the two callees still consume it.
- **The Go code needs no transfer.** `newSnapshotReaderCloser`'s `go func()` (`snapshot_merge.go:58`)
  gets its own token from the fork (`wp_fork_tok_body`). The caller's token need not move.
- **Who is affected:** K6's merged snapshot to a lagging follower, and the snippet `ReqMergedSnapshot`.
- **Fix:** both posts return `threadTok`.

### N4. `Start.spec` consumes the caller's only `threadTok`

- **The leak.** `EtcdServer.Start.spec` takes `threadTok` and returns `isServer ∗ srvGate s 1 ∗
  srvRunning`, without the token. Its sketch says the token goes to the read loop ("the caller's
  one token for the read loop"). That was the old `GoAttach` shape.
- **The token can now come back.** `GoAttach.spec` now gives the goroutine a fresh token and returns
  the caller's (C45). Lowercase `start` takes none, since `go s.run()` forks a fresh token.
- **Snippets that do not close:**
  - `etcdserverboot/boot.go` `ReqStartThree` calls `s.Start()` three times in a loop with one token;
  - `ReqRestart` calls `put(s, …)`, whose spec takes `threadTok`, after `ReqStartOne`'s `Start`, and
    later `s2.Start()` and `get`.
  - The same pattern appears in `examples/lib/etcdstart`, `cluster3`, putget and the other users the
    header lists.
- **Fix:**
  - `Start.spec`'s post adds `threadTok`;
  - the sketch's token accounting follows C45 (each attached goroutine's fresh token; the read loop's
    `readLoopTok` from `isServer`'s realization).
- **Status:** not in A8's reports. It is in my scope through `ApiBoot`/`EtcdServer__*`.

### N5. The new bridge `srvNode_member : srvNode ⊢ srvMember` cannot be realized

- **What the law needs.** `srvMember`'s stated realization (`ApiBoot.lean:108`) includes the
  read-only field `r.transport` with 2f's `isTransport`. `CutPeer`, `MendPeer`, `PauseSending` and
  `ResumeSending` need it, since they read `s.r.transport`.
- **When `srvNode` must already hold.**
  - `srvNode` must hold from the server literal on, "before `tr.Start()`: `Process` may be called
    from then on" (`ApiApply.lean:276`).
  - `srvNode_raftOk` builds rafthttp's `raftOk` from it, and `Process.spec` takes `srvNode`.
  - In Go, `tr.Start()` and the `AddPeer` loop, whose stream readers may deliver to `Process`, run
    at `server.go:424-437`. `srv.r.transport = tr` is assigned only afterwards (`server.go:438`).
- **The contradiction.** A persistent `srvNode ⊢ srvMember` would give a read-only points-to of
  `r.transport` (then `nil`) at a point where the field is later written.
- **Who is affected:** the apply side's `Logger`, `isLeader`, `RequestTimeout`, `AppliedIndex` and
  `FeatureEnabled` calls. These are A7-provability F2's remaining source of `srvMember` for:
  - `applySnapshot`;
  - `createMergedSnapshotMessage`;
  - `applyConfChange`;
  - `applyEntryNormal`'s `isLeader`;
  - `ensureLeadership` from `revokeExpiredLeases`.
- **Fix (either):**
  - (a) split the fields the literal sets (`lgMu`/`lg`, `Cfg`, `memberID`, `cluster`) into a
    predicate implied by `srvNode` (say `srvFields`), and have the getters take that. Keep
    `srvMember` (with the transport) for the peer methods only.
  - (b) restate the bridge as `srvNode ∗ srvStarted ⊢ srvMember`, and carry `srvStarted` (or
    `srvMember` itself) in `applyThread`. Today `applySnapshot` and `createMergedSnapshotMessage`
    hold no `srvStarted`.

  (a) is the more local fix.

## Regressions checked: what closes

96 spec files in scope changed since `1aa6fc1337`: 25 added, 71 modified. I read every changed
statement. Every one closes apart from N1-N5 and the items below.

**Request path.**
- `processInternalRaftRequestOnce` and `raftRequest` close with the new
  `FeatureEnabled.spec` (`srvMember` from `isServer_member`, `threadTok`).
- `Compact` closes at `phys = false` without the gate. Go reads `s.kv.Rev()` after `kv.Close()`,
  and 3e's `revRd γ true` covers that. `ForceCommit` runs only when `phys`, under the gate.
- `LeaseRevoke` closes without the gate (no `Cleanup` before `s.wg.Wait()`).
- `srvHdrReply`, `replyHdrOwn_header` and `ltlReply_replyHdr` give `hdr.fill` its non-`nil` header.
- `txnChecked_admitted` is plausible: `checkIntervals` refuses duplicate puts in a branch.

**Read path.** `ensureLeadership`, `EtcdServer.LinearizableReadNotify` and `readEnv`'s rows close
over `Read.LinearizableReadNotify` (`threadTok`, `readAt s.read γ.raft (srvApplied s γ)`) and
`AppliedIndex`'s post (with `srvNode_agree`).

**Apply side.** The token threading closes through `Schedule.funcOk`, except N3.

**`cindex`.** `ciCells` and `txStoredCI_sess` are plausible. `UnsafeSave` writes the two
`meta` cells. The `beCur ciCells` question is recorded in "Gaps left open".

**`schedule`.** `funcOk`/`jobOk` now lend `threadTok`. mvcc's compaction jobs must thread it (not my
area).

**Snippets.** All changed or added snippets in `etcdserverreq` and `etcdserverboot` were checked:
- **Close:** `ReqCompactorCompact`, `ReqCompactorInternal`, `ReqRefusalNotApplied`,
  `ReqExpiryRevoke`, `ReqKeepAliveFollower`, `ReqLeaseReplyHeader`, `ReqReadErrIndef`,
  `ReqPartition`, `ReqReadyOrStop`, `ReqMemberListAfterAdd`, `ReqGetters`, `ReqLockOverInProc`.
  - `ReqExpiryRevoke` has no `rootTokOk` for simple tokens (§6 F2), and does not state `reqCtxOk`
    or `Context.ctxOk` of `ctx`.
  - `ReqGetters` does not state the `threadTok` that `Backend`, `ClusterVersion` and
    `FeatureEnabled` take.
- **Do not close:**
  - `ReqReadAfterWrite` (N2);
  - `ReqStartThree` and `ReqRestart` (N4);
  - `ReqMergedSnapshot` (N3), unchanged but now broken.
- The completeness report's missing patterns are now covered:
  - the internal requester without a gate (`ReqCompactorInternal`, `ReqExpiryRevoke`);
  - `LinearizableReadNotify`;
  - the getters;
  - `MemberList`.
- The closure-before-start shape (`compactable`, `ckptOk`) still has no snippet. That is second
  tier, and the place where N1 would have shown.

**Second tier.**
- `srvStarted`'s stated content says only "`s.ctx`". It should state `s.ctx` is
  `WithCancel(Background())`, with `Context.ctxOk ∗ reqCtxOk ∗ ctxNoIncoming`. Every internal
  requester's sketch relies on that: `revokeExpiredLeases`, the `NOSPACE` alarm, `ensureLeadership`,
  `publishV3`.
- `ReqCompactorInternal` does not name its update's source (`envUpd`, `EnvStep.compact`).
- `beReadable` is still provisional (recorded).

## Counts

- **Original first-tier findings:** 17 (provability F1-F8, completeness F1-F6, plus the recorded
  F9/F10).
  - Resolved: 11.
  - Partly resolved: 2 (P-F2, C-F2).
  - Resolved apart from a recorded gap: 1 (P-F4).
  - Open decisions or recorded: 3 (F8 → 5.1; F9; F10).
- **Spec files re-checked:** 96, all changed since `1aa6fc1337`. 91 close; 5 do not
  (`createMergedSnapshotMessage`, `newSnapshotReaderCloser`, `applyAll`, `Start`, the law
  `srvNode_member`).
- **Laws checked:** all new laws in `ApiReq`, `ApiApply`, `errors`, `read`, `cindex` and `schedule`.
  1 cannot be realized (`srvNode_member`); none is vacuous.
- **Snippets checked:** 16, changed or added. 12 close; 4 do not (`ReqReadAfterWrite`,
  `ReqStartThree`, `ReqRestart`, `ReqMergedSnapshot`).
- **`go vet`:** clean on all six packages.

No new bug in the Go code.
