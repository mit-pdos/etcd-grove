# Fix plan: the `issues/` findings the specs sidestep (2026-11-10)

The user's rule (2026-11-10, `open-questions.md` D, "The user's answers", 2.8): *"If we have a failing
etcd test case, we should make a fix and then prove the fixed code."* So every `issues/` finding that
the specs-only branch sidesteps (a premise, an environment/workload/scope premise, a weakened post, a
model admitting the buggy behavior, a "**Now:**" workaround) gets a fix on its Goose fork (etcd:
`upamanyus/etcd` `goose-lean`, pinned `a4d2bb172`; raft: `raft37-goose-lean-a2`, pinned `565c2bd`;
bbolt: `upamanyus/bbolt` `goose-lean`, pinned `743299d8`), a re-translation, and a spec of the fixed code.

Research only: nothing here has been applied, translated or built. "Go test passes" says how it is
known; every fix branch below is off **upstream** `main`, not the fork, so each must be re-run after
the cherry-pick onto the fork.

**The goal path** (`top.md` §2, K6): `examples/etcd/txnlin`, one member started by
`etcdstart.StartServer` (auth off, no leases, auto-compactor off, `MaxTxnOps` 128,
`MaxRequestBytes` 1.5 MiB, snapshot count 10000), a default client (`etcdstart.NewClient`), the
workload `genFrom` (get, unsorted range list, put, delete, txns of 1-3 ops on distinct keys, a CAS with
one `Then` put and one `Else` get: **no** compare-only txn, keys-only read, sort, limit, nesting, watch,
lease, auth, compaction, member change, stop), with Perennial crashes at any point. Three degrees in
the table's second column:

- **goal: premise** -- the adequacy theorem (or a spec on its path) carries a premise because of the
  bug, which txnlin cannot discharge from its own code (an opaque environment/workload `Prop`);
- **goal: met** -- a premise on the goal path that txnlin's configuration or workload meets (it is
  discharged, but it is the bug's sidestep and goes with the fix);
- **goal: model** -- W0's model (`SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`), which txnlin's proof
  reasons over, admits the bug; txnlin's workload never reaches it;
- **no** -- reached only by other users (multi-member, leases, auth, watch, k8s, leasing, cache,
  concurrency, recipes); the user in brackets.

## Already fixed, or not on a fork (skipped)

**Fixed on the pinned forks** (`etc/goose.py`'s project comments; the specs state the fixed code), 26:
`bbolt-commit-meta-error-frees-reader-pages`, `bbolt-writeto-meta-parity`, `cache-ready-after-retry`,
`etcd-alarm-store-snapshot-race`, `etcd-auth-grant-permission-same-key`,
`etcd-auth-snapshot-closed-backend-panic`, `etcd-backend-duplicate-put-stale-read`,
`etcd-compact-past-raft-applied`, `etcd-compaction-delete-then-put`,
`etcd-leader-advance-before-applyconfchange`, `etcd-lease-close-require-leader-ctx-misaligned`,
`etcd-merged-snapshot-stale-term`, `etcd-quota-stale-backend-after-snapshot`,
`etcd-release-snapdb-before-open`, `etcd-txn-delete-then-ignore-put` (#22395 as `249d76bea`; 3b's
`Txn.txnSafe`, `apply/Api.lean:560-570`, is discharged by the fixed `checkIntervals`),
`etcd-unary-interceptor-learner-removed`, `etcd-watch-progress-before-created`,
`etcd-watch-progress-closed-substream`, `etcd-watch-resume-below-start-revision`,
`etcd-watch-resume-closing-substream`, `raft-readindex-removed-leader`, `raft-readindex-singleton-stale`,
`raft-snapshot-during-apply-stale-confchange`, `raft-stale-term-appresp-index-zero-ack`,
`recipes-barrier-wait-closed-watch`, `recipes-dequeue-closed-watch`.

**Not in any of the three forks' pinned code**, 9: `go-itab-reinterpret-assert`,
`go-overlapping-named-array-copy` (the Go toolchain; fixed in the pinned go1.27.x);
`bbolt-txstats-unaligned-32bit` (introduced by bbolt#1300, after the pin; 32-bit only);
`grpc-codec-alloc-before-size-check` (grpc-go, a trust boundary; its etcd-side half is fix E2 below);
`k8s-apiserver-compactor-missing-key-panic`, `k8s-clientgo-getindexers-unlocked-map`,
`k8s-daemonset-ambiguous-create-duplicate-pod`, `k8s-etcd3-cached-noop-skips-preconditions`
(blocks-proof: yes for the k8s etcd3 driver), `k8s-workqueue-exponential-backoff-2to63` (Kubernetes,
translated from its module, no fork; the specs-only branch has no k8s apiserver/client-go specs:
`SpecPlan/Spec/k8s_io/` holds only `utils`). A Kubernetes fork would be a fourth fork: the user's call.

That leaves **55** findings, below. **16** of them touch the goal path (2 goal: premise, 9 goal: met,
4 goal: model, 1 goal-path code with no premise); **7** need no spec change (R5, R6, E29-E32, B5:
documentation only, an unspecified mode, liveness, a metric, partial correctness): fix optional.

## The table

Effort: S (a few lines of Go, a local spec edit), M (a function's logic, or several specs), L (a new
proof argument or a cross-cutting spec change). `F#` are `open-questions.md` §6's numbers.

| # | slug | goal path? | current handling (file:line) | fix | fork | effort | spec changes |
|---|---|---|---|---|---|---|---|
| R1 | raft-commit-lost-with-entries-kept | **goal: premise** (`Wal.crashInScope` in the adequacy theorem) | `Recs.confAboveOk`/`crashScopeOk`/`crashInScope`, `storage/wal/Api.lean:256,277,285`; `raftState_crash.spec`'s `D'.confAboveOk`, `raft/v3/Api.lean:1027`; `Durable.confAboveOk`, `raft/v3/Model.lean:341`; `ApiBoot.lean:233-247` (F8) | raft restart infers commit: in `newRaft`, raise `committed` to the second-to-last conf-change entry above it (all but the last are committed); alt. etcd-side atomic `Save` | raft | L | drop `confAboveOk` from `raftState_crash`; `crashScopeOk` keeps only part (b); new raft invariant |
| R2 | raft-zero-max-size-per-msg | goal: met (etcd: 1 MiB) | `ConfigOk`'s `MaxSizePerMsg ≠ 0 ∨ MaxCommittedSizePerReady ≠ 0`, `raft/v3/Api.lean:519-522,535` | `validate` defaults `MaxCommittedSizePerReady` when both are 0, or `nextCommittedEnts` hands out one entry at budget 0 | raft | S | delete the `ConfigOk` conjunct |
| R3 | raft-memorystorage-initialstate-unlocked | goal: met (one call in `newRaft`) | `InitialState` reads unlocked, needs the contents exclusively: `MemoryStorage__InitialState.lean:4-6`; `memStor`'s split footprint, `raft/v3/Api.lean:95-101` | take `ms.Lock()` in `InitialState` (raft#547; `15190e3`) | raft | S | `InitialState` over the lock; `memStor` loses its unlocked share |
| R4 | raft-config-clone-autoleave | goal-path code, no premise (`Changer` clones) | `Config.Clone.spec` states `autoLeave := false`, `tracker/Config__Clone.lean:9` | `AutoLeave: c.AutoLeave` in `Clone` | raft | S | `Clone`'s post copies `autoLeave` |
| R5 | raft-advance-before-applyconfchange | goal: met (the fork's leader wait, `4d9282b0f`) | `node.Advance`: unapplied conf entries "decided skip", `raft/v3/node__Advance.lean:18-19` | documentation (`fd30b41`: conf changes applied before `Advance`); no code | raft | S | none (the premise is then the documented contract, which etcd's fork meets) |
| R6 | raft-async-snapshot-during-apply-divergence | no (etcd sets no async writes) | `ConfigOk`'s scope `AsyncStorageWrites` off, `raft/v3/Api.lean:524-527` | `b60b90c` (`rawnode.go`) | raft | M | none unless the async mode is specified (it is unspecified, not sidestepped) |
| E1 | etcd-txn-nested-depth-apply-panic | goal: met (128 ≤ 4999) | `maxTxnOpsMax = 4999`, `v3rpc/Api.lean:169-171`; `NewKVServer.lean:6`; `IrrBody.depthOk`, `ApiReq.lean:69,226` | bound the nesting depth in `checkTxnRequest` (`v3rpc/key.go`), independent of `--max-txn-ops` | etcd | S | delete `maxTxnOpsMax` from `isServer`/`NewServer`; `depthOk` from the check's post |
| E2 | etcd-txn-keysonly-reply-alloc-panic | **goal: premise** (`Grpc.msgsFit`, server half) | `msgsFit` on `Server.Serve`/`start`, `grpc/Api.lean:28-38,210,850,859`; `Server__Serve.lean:14` | count nested ops toward `--max-txn-ops` (`7a63f2b96`, `key.go`) **and** size check before `proto.Marshal` in etcd's server `codec` (`v3rpc/codec.go`) | etcd | M | server half of `msgsFit` deleted (`Server.Serve`, `start`); client half stays (grpc-go) |
| E3 | etcd-txn-check-intervals-sibling | goal: model (putOnce) | `putOnce` admits a delete after a put, `Model.lean:795-799`; `exactFrom` gate, `Model.lean:196-207` (77 uses; A17, C9, C11) | reverse pass in `checkIntervals` (`fc6254021`, `key.go`) | etcd | M | `putOnce` → each key changed at most once; `exactFrom` becomes a law from `Reach`, its gates deleted |
| E4 | etcd-txn-empty-serializable | goal: model | `∃ v, if t.readonly ∧ t.serializable then σ.kv.IsView v`, `Model.lean:1040-1045,47`; `IsTxnSerializable.lean:9-10`; `EtcdServer__Txn.lean:29` | `IsTxnSerializable` false for a txn with no ops (`e3010762c`, `txn/txn.go`) | etcd | S | `TxnReq.serializable` false at no ops; txnlin's Gen restriction (top.md §2) gone |
| E5 | etcd-range-sort-none-limit | goal: model | `pushdownLimit` quirk, `Model.lean:45,597-603` | read the whole range before a NONE-order sort (`6cb3f6108`, #22616, `txn/range.go`) | etcd | S | `pushdownLimit` tests the effective order |
| E6 | etcd-range-keys-only-lease | goal: model | `fastKeysOnly` zeroes the lease, `Model.lean:46,633-646`; `kv__Get.lean:21`; leasing `Api.lean:159` | turn off `FastKeysOnly` (`txn/range.go:67`); upstream #22550 is the larger alternative | etcd | S | delete `fastKeysOnly`'s lease clause |
| E7 | etcd-client-resolver-build-race | goal: met (AutoSync 0; `New`'s own `SetEndpoints`) | `resolverIdle`, `ApiClient.lean:280-287`; `cfgOk`'s `AutoSyncInterval = 0`, `ApiClient.lean:79-84`; `Client__SetEndpoints.lean:12,43` (C1) | a mutex in `EtcdManualResolver` over `endpoints`/`serviceConfig` in `Build`, `SetEndpoints`, `updateState` (`client/v3/internal/resolver`) | etcd | M | delete `resolverIdle` and `cfgOk`'s auto-sync clause; `autoSync.spec` for any interval; trusted resolver specs change |
| E8 | etcd-client-dial-empty-endpoints | goal: met (non-empty endpoints) | `epsTok` fraction at a non-empty list, `ApiClient.lean:66-75`; `Client__dial.lean:6-7`; `maintenance__Status.lean:15` | `dial` reads `endpoints` under `epMu` and fails on an empty list | etcd | S | `dial`/`Status` lose the `epsTok` premise (an error disjunct) |
| E9 | etcd-auth-useradd-long-name-fatal | goal: met (auth admin ops never sent) | `Auth.recordsFit` scope, `auth/Api.lean:251-260,662`; `nextOk`, `apply/Api.lean:797-806`; `authStore__UserAdd.lean:10` | `UserAdd`/`RoleAdd` reject names > `MaxKeySize` (`612320b8e`, `auth/store.go`) | etcd | S | `recordsFit`'s name half becomes an error disjunct of W0's `userAdd`/`roleAdd` step; the value half stays (`nonissues/etcd-auth-record-too-large-fatal.md`) |
| B1 | bbolt-max-value-size-unusable | goal: met (requests ≤ 1.5 MiB) | `bboltEntryMax = 2^28` premise of `Put`, `bbolt/Model.lean:127-136`; `Bucket__Put.lean:20,56` | `Put` rejects a value too large to store with its key (`668f5c0`, `bucket.go`) | bbolt | S | with B2: `Put`'s premise → `ErrValueTooLarge` disjunct; etcd's backend keeps a size premise from the request path |
| B2 | bbolt-large-values-leaf-unreadable | goal: met | same `bboltEntryMax`; `Bucket__spill.lean:7`; `Internal.lean:453` | split a node too large for one page (`b71c0a2`, `node.go`) | bbolt | M | `spill`'s fit argument re-stated; `bboltEntryMax` deleted |
| E10 | etcd-read-after-backend-close-panic | no (txnlin never stops; a sole member does not self-stop) | drain premise: `HardStop`/`Stop` take `srvGate s 1`, `EtcdServer__HardStop.lean:21-25`, `ApiBoot.lean:65-71`; `run.spec`'s errorc scope text, `EtcdServer__run.lean:54-61` (A7, C46, F3) | a stop gate: reads take it shared, `Cleanup` exclusively after marking stopped, later reads `ErrStopped` (`server.go`, `v3_server.go`) | etcd | L | the drain premise and `run`'s scope text deleted; request specs gain an `ErrStopped` disjunct |
| E11 | etcd-mvcc-hash-currentrev-race | no [multi-member corruption check, `Hash` RPC] | `mvccRestoreGate`, `mvcc/Api.lean:216-221`; `hashStorage__Hash.lean:2`; `applySnapshot.spec`'s scope, `EtcdServer__applySnapshot.lean:42` (A8, F13) | cherry-pick #22609 (`7ff040cb8`, `kvstore.go`) | etcd | S | `Hash`'s share of the gate dropped; `HashByRev`'s stays unless E12 |
| E12 | etcd-mvcc-hashbyrev-restore-rev1 | no [corruption check] | `hashStorage__HashByRev.lean:2` (current revision may be `1`) | read `currentRev` under `s.mu.RLock` in the stored-hash path (`hash.go`) | etcd | S | `HashByRev`'s post: a revision the store had |
| E13 | etcd-restore-scheduled-compact-zero | no [compactors, k8s] | `rev ≠ 0` scope: `KV.CompactTriple`, `client/v3/Api.lean:747-750`; `EtcdServer__Compact.lean:8-13,26`; `mvcc/Api.lean:417` | reject `Compact(rev ≤ 0)` with `ErrCompacted` (closes E14 too); or `fix.patch` (`kvstore.go` restore) | etcd | S | the `rev ≠ 0` scope deleted (client, server, mvcc) |
| E14 | etcd-mvcc-hashbyrev-zero-stored | no [corruption check] | `hashStorage__HashByRev.lean:2`; E13's scope | E13's rejection | etcd | S | as E13 |
| E15 | etcd-mvcc-watch-compacted-after-progress-restore | no [watch] | compaction checked against `posEvOf`, `mvcc/ApiWatch.lean:195-201`; 1b weakened alike | raise a synced watcher's `minRev` to progress+1 on a progress (`watchable_store.go`) | etcd | S | `wStep`/`watchStep` check compaction against `posOf` |
| E16 | etcd-watch-compacted-resent | no [watch, >512 watchers] | `watcherGroup.choose.spec` states it, `watcherGroup__choose.lean:5`; `mvcc/ApiWatch.lean:43` | #22295 (`choose` deletes compacted watchers from the group) | etcd | S | `choose`'s post; `wStep` no repeated compaction |
| E17 | etcd-watch-current-resume-past-event | no [watch] | `WatchPos.init`'s floor, `client/v3/ApiWatch.lean:34-46`; `watcher__Watch.lean:68` (F14) | the created response carries the registration revision; the client resumes from it + 1 | etcd | M | `rev = 0` watch complete from its creation revision |
| E18 | etcd-watch-id-reuse-stale-events | no [gateway, foreign clients] | wire scope: creates carry `WatchId = 0`, `v3rpc/ApiWatch.lean:40-52`; `watchStream__Watch.lean:38` | `2e9028084` (`v3rpc/watch.go`) | etcd | M | the wire-request scope's id clause deleted |
| E19 | etcd-watch-prevkv-before-created | no [k8s watches] | loose `prevOk`, `v3rpc/ApiWatch.lean:26-28`; `WatchInternal.lean:32`; `sendLoop.lean:19`; `recvLoop.lean:38`; `WatchPos.prevLoose`, `client/v3/ApiWatch.lean:63-67` (F4) | `recvLoop` holds `sws.mu` across mvcc's `Watch` and the option writes, or `sendLoop` looks up `prevKV` at flush (`v3rpc/watch.go`) | etcd | M | `prevOk` strong; `prevLoose` deleted |
| E20 | etcd-v3lock-watch-shared-stream-principal | no [v3lock/v3election with auth] | in-process stream outside the contract, `v3rpc/ApiWatch.lean` header; `client/v3/streamKeyFromCtx.lean` | copy the caller's auth metadata to the outgoing context (`v3lock`/`v3election`) | etcd | M | per-call principal through the in-process watch |
| E21 | etcd-stream-interceptor-err-before-done | no [require-leader streams] | `newStreamInterceptor.lean:6` claims the wrapped context; `sicEtcdOk` opaque (unrealizable as stated) | `8330458d9` (`v3rpc/interceptor.go`) | etcd | S | `cancellableContext` meets `isContext`: `sicEtcdOk` realizable |
| E22 | etcd-rangestream-auth-revoked-midstream | no [auth, streamed range] | `ErrAuthOldRevision` after every chunk, `EtcdServer__RangeStream.lean:20,64` | re-check the auth revision before each page | etcd | S | the post's stale-auth-after-sends outcome deleted |
| E23 | etcd-rangestream-sort-none | no [streamed range] | contents not modelled, `client/v3/Api.lean:480` | `638081c75` (or #22615) | etcd | S | model `RangeStream`'s contents (M, separate) |
| E24 | etcd-lease-id-mask-member-prefix | no [multi-member leases] | grant may answer `ErrLeaseExist`, `Model.lean:1068-1069`; `EtcdServer__LeaseGrant.lean:9` | `e840fe4b6` (check against upstream #20729 first) | etcd | S | the `ErrLeaseExist` disjunct for a server-chosen id deleted |
| E25 | etcd-lease-timetolive-keys-toctou | no [leases + auth] | margin: checked keys, not returned ones, `EtcdServer__LeaseTimeToLive.lean:22` | `IsRangePermitted` on the returned `resp.Keys` | etcd | S | the margin closes: keys returned only if readable |
| E26 | etcd-leasehttp-timetolive-nil-response-panic | no [follower `TimeToLive`] | `leasePeerURL` deployment premise, `lease/leasehttp/Api.lean:15-19`, `TimeToLiveHTTP.lean:18` (C24, D8, D15) | `if lresp.LeaseTimeToLiveResponse == nil \|\| ...Header == nil { return error }` (`leasehttp/http.go`) | etcd | S | `TimeToLiveHTTP`'s `leasePeerURL` premise deleted (`leaseURLOf` gating stays for the view) |
| E27 | etcd-leasehttp-timetolive-nil-header-panic | no | same | same patch | etcd | S | same |
| E28 | etcd-rafthttp-stream-dial-bad-server-version-panic | no [non-member at a peer URL] | margin + `verHdrOk` premise, `rafthttp/serverVersion.lean:10`, `minClusterVersion.lean:10` | parse with `semver.NewVersion`, fail the dial (#21829) | etcd | S | `serverVersion`/`minClusterVersion` return an error, no header premise |
| E29 | etcd-applied-index-stale-after-snapshot | no [follower after a snapshot] | refusal allowed by W0 (`Step.refuse`); `specreq/etcdserverapply/apply.go:40` | #22510 (`applySnapshot` stores the applied index) | etcd | S | none required (liveness); optional: `appliedIndex` exact |
| E30 | etcd-restore-pending-compaction-unclosed | no [compaction + snapshot] | `compactChanOk`: "or never", `mvcc/Api.lean:275-282` | close `ch` on `stopc` in `compactBarrier` | etcd | S | none required (liveness); optional: channel always closed |
| E31 | etcd-watch-close-hang-refused-create | no [watch] | partial correctness, `client/v3/watcher__Close.lean:13` | add the refused watch to `closing` (`client/v3/watch.go`) | etcd | S | none (liveness) |
| E32 | etcd-apply-alarm-gauge-reactivate | no | not modelled (a metric) | count only newly added alarms | etcd | S | none |
| C1 | cache-stale-progress-compacts-newest-watch | no [cache] | cache tolerates a spurious compaction cancel, `batch-1g.md:71-74`; trigger fixed in the fork (`09669450f`) | `Broadcast` checks progress against `max(maxRev, minRev-1)` (`cache/demux.go`) | etcd | S | the spurious-cancel case leaves `Cache.Watch`'s post |
| L1 | leasing-modify-uncached-once | no [leasing] | writes persistent, any number of times, `leasing/Api.lean:26-34`; `leasingKV__Put.lean:26` (F5) | `7a6077dec` | etcd | M (L1-L9) | with L1-L9 and `nonissues/leasing-write-resend-after-error`: leasing meets `KV.*Triple` (W0's exclusive update, serializable cached answers, no marks) |
| L2 | leasing-update-stale | no | `CachedRange`, `lkvMarks`, `leasing/Api.lean:49-55`; `leaseCache__Update.lean:3` | `d97e455c2` | etcd | | (L1) |
| L3 | leasing-get-failed-acquire-options | no | `leasing/Api.lean:50`; `leasingKV__get.lean:12` | `af95e2ff8` | etcd | | (L1) |
| L4 | leasing-evalcmp-missing-key | no | wrong branch admitted, `leasing/Api.lean:56,184`; `evalCmp.lean:3`; `txnLeasing__Commit.lean:28` | `06541aec6` | etcd | | (L1) |
| L5 | leasing-evictrange-key | no | `leaseCache__EvictRange.lean:3` | `14d1c4bf3` | etcd | | (L1) |
| L6 | leasing-stale-entry-after-reset | no | cached answers "serializable at best", `leasing/Api.lean:35-40`; `specreq/leasing/unmet.go:33` | `3d0769edc` | etcd | | (L1) |
| L7 | leasing-wait-rescind-no-delete | no | `waitRescind` may return `nil` with no promise, `leasingKV__waitRescind.lean:3` | `d3db62afd` | etcd | | (L1) |
| L8 | leasing-delete-range-drops-prevkv | no | `execReq` drops `prevKv`, `leasing/Api.lean:61-64` | pass the `Op`'s `prevKV` to `deleteRangeRPC` (not written) | etcd | | (L1) |
| L9 | leasing-delete-fromkey-skips-revoke | no | past-state record only (weakened) | map end `"\x00"` to `GetPrefixRangeEnd(pfx)` in `revokeRange`, `deleteRangeRPC`, `guardRanges` (not written) | etcd | | (L1) |
| K1 | mutex-lock-recreated | no [concurrency] | `lockedSince`: create revision `≥ c`, `concurrency/Mutex__Lock.lean:32,41`, `concurrency/Api.lean:26,191` (F12) | `b1d4bb04b` (#22617) | etcd | S | `Lock`'s post `holdsAt` at the header's state |
| K2 | stm-serializable-snapshot | no [STM] | a failed attempt's reads promise nothing, `concurrency/NewSTM.lean:26`, `concurrency/Api.lean:47` | `928618847` | etcd | S | every attempt reads one revision |
| B3 | bbolt-deletebucket-nested-leak | no (etcd's `DeleteBucket` is top-level) | `Bucket.ForEachBucket.spec_del` (C48), `Bucket__DeleteBucket.lean:13`, `Bucket__ForEachBucket.lean:12` | bbolt#1305 (collect child keys, then delete) | bbolt | S | `spec_del` deleted: `DeleteBucket` over the public `ForEachBucket.spec` |
| B4 | bbolt-cursor-prev-empty-leaf | no (etcd never calls `Prev`) | `Prev.spec` restricted to read txns, `Cursor__Prev.lean:8` | skip empty leaves in `Prev` as `Next` does (not written) | bbolt | S | `T.rw = false` scope deleted |
| B5 | bbolt-cursor-last-empty-leaves-hang | no | partial correctness, `Cursor__Last.lean:5` | skip empty leaves in `Last` (not written) | bbolt | S | none (a hang meets any post) |

## Per-fix detail

### Goal path

**R1, raft-commit-lost-with-entries-kept** (raft; `Wal.crashInScope`'s part (a) in K6's adequacy
premise). The user's 2.8 answer deletes the conf-change part.

- *Fix (recommended, raft):* in `newRaft` (`raft.go`), after the log and `HardState` are loaded and
  unless `DisableConfChangeValidation`, scan the conf-change entries in `(committed, lastIndex]`; if
  there are two or more, `raftLog.commitTo` the index of the second-to-last. Why it is sound: a leader
  appends a conf change at `j` only when `pendingConfIndex ≤ applied` (`raft.go`'s `stepLeader`
  check; `appliedTo`'s auto-leave entry likewise), and `pendingConfIndex` is at least every earlier
  entry's index (set to `lastIndex` at `becomeLeader`, to the entry at a proposal), so an earlier
  conf change `i < j` in the same log (log matching) was applied, hence committed, by that leader.
  After the restart the existing guard (`hasUnappliedConfChanges` over `(applied, committed]`) sees
  the earlier change, the node applies it before campaigning, and at most one conf change stays
  above the commit: the safe single-change case. Liveness is untouched (unlike the issue's other
  suggestion, refusing to campaign while any conf change is above `applied`, which deadlocks a
  cluster whose leader died with a replicated, uncommitted conf change).
- *Alternative (etcd):* make `wal.Save` batch-atomic: always end a `Save` with entries by a state
  record (the WAL's last `HardState` if `st` is empty), mark it (a new record type, so old WALs are
  read as before: an old WAL legitimately has entries with no state record after them), and have
  `ReadAll` drop entry records after the last marker. Changes the WAL format and the trusted WAL model
  (`walRecs_crash`): a trusted-boundary change for the user, so second choice.
- *Test:* `TestRestartWithEntriesButNotCommit` must be checked with the fix: node 1 then applies
  index 2 before campaigning and loses in `{1, 2}`; the test asserts index 4 equal on nodes 3 and 1,
  which may need the partition healed to give node 1 an index 4 (read its end before relying on it).
- *Risk:* behavior change only at a restart with two conf changes above the stored commit (rare); the
  inferred commit is true. Upstream: a novel inference in raft; reviewers may prefer the doc +
  application-side atomicity route. Gate it behind `!DisableConfChangeValidation` (the argument needs
  validation on every leader).
- *Specs:* `raftState_crash.spec` (`raft/v3/Api.lean:1024-1031`) loses `D'.confAboveOk`; delete
  `Durable.confAboveOk` (`Model.lean:331-343`) and `Wal.Recs.confAboveOk` (`wal/Api.lean:256`);
  `Recs.crashScopeOk` becomes part (b) only (no snapshot record above the commit: a spec limitation,
  no `issues/` finding; it stays an environment premise until separately addressed); `ApiBoot.lean`'s
  scope text (`:233-247`) and `top.md` K6 follow. R1's realization needs the invariant "in every log,
  a conf change followed by a later one is committed" (from the leader's `pendingConfIndex` check):
  the L part.

**E1 + E2 + E3, one change to `checkTxnRequest`/`checkIntervals`** (etcd `server/etcdserver/api/v3rpc/
key.go`, plus `codec.go`).

- *E1 (nested depth):* a depth parameter in `checkTxnRequest`, refusing (`ErrGRPCTooManyOps` or a new
  `InvalidArgument`) beyond a fixed bound well below protobuf's 10000/2 (e.g. 64), independent of
  `--max-txn-ops`. Not written; its test `TestTxnNestedDeep` must be checked (needs `--max-txn-ops`
  ≥ 5000 to reach the old panic; with the fix it gets the refusal). Risk: refuses deeply nested txns
  that are legal today (none in practice). Spec: `maxTxnOpsMax` and its `isServer` clause go
  (`v3rpc/Api.lean:169-171`, `NewKVServer.lean:6`); `IrrBody.depthOk` (`ApiReq.lean:69,226`) follows
  from the check's post; `MarshalIRR`'s depth premise is met by every admitted request.
- *E2 (keys-only reply):* `7a63f2b96` counts every nested txn's operations toward the limit (the
  test `TestCheckTxnRequestNestedOps`/`TestV3TxnNestedTooManyOps` fails at its base and passes on the
  branch, its PR draft). That bounds the reply only by `--max-txn-ops × keyspace`, so for the proof
  also check the size in etcd's server codec (`v3rpc/codec.go`, `codec.Marshal`: `proto.Size(m) >
  math.MaxUint32` → `status.Error(codes.ResourceExhausted, ...)` before `proto.Marshal`), which
  removes the panic whatever the configuration. `codec`'s methods are untranslated today
  (`Code/.../v3rpc.toml:39` lists the type only): add `codec.Marshal`/`Unmarshal` to the toml. Spec:
  the server half of `Grpc.msgsFit` (`grpc/Api.lean:210,850,859`; `Server__Serve.lean:14`) is no longer
  needed for etcd's server (its codec's spec returns `ResourceExhausted`); the client half (`NewClient`'s
  `msgsFit`, grpc-go's own codec, `grpc-codec-alloc-before-size-check`) stays a goal-path premise
  unless etcd's client registers the same checked codec (an etcd change upstream would question) or
  grpc-go is fixed. Risk: none for valid traffic.
- *E3 (sibling put/delete):* `fc6254021` (+25 lines in `key.go`; its unit test in `key_test.go`; the
  issue's integration tests `TestTxnSiblingPutThenDelete`, `TestWatchFromCompactRevAfterSiblingPutDelete`
  must be checked on the fork). Risk: refuses a txn upstream accepts today (it already refuses the
  reverse order); upstream's #16395 objection was cost, which the reverse pass answers. Spec: W0's
  `putOnce` (`Model.lean:795-799`) becomes "each key changed at most once in a transaction's events";
  then every committed revision changes each key at most once, so `exactFrom` is a law
  (`etcdLb_exact`: `Reach` keeps it) and its 77 gates (A17, C9, C11; `client/v3/ApiWatch.lean`,
  `mvcc/ApiWatch.lean`, `cache/v3/Internal.lean`, recipes, 1d `Observe`) can be deleted. A large but
  mechanical deletion; `nonissues/etcd-mvcc-watch-compact-rev-subrev-lost.md` stays covered (no gRPC
  revision changes a key twice).

**E4, etcd-txn-empty-serializable** (`server/etcdserver/txn/txn.go`, `IsTxnSerializable`): `e3010762c`
(4 lines); the test `TestTxnCompareOnlyLinearizable` fails at its base and passes on the branch (its PR
draft). Risk: a compare-only txn now waits for the read index. Spec: W0's `TxnReq.serializable` false
at no operations, so `Model.lean:1040-1045`'s stale view covers only txns whose ranges asked for it;
`IsTxnSerializable.lean`'s changes line; `top.md` §2's txnlin scope point deleted (its generator no
longer needs to avoid compare-only txns).

**E5, etcd-range-sort-none-limit** (`txn/range.go`): `6cb3f6108` (#22616, open; a maintainer agreed
with the problem); test passes on the branch (PR text). #22615 (another author) makes
`IsDefaultOrdering` false for a non-key target with NONE, which also fixes E23. Spec:
`RangeReq.pushdownLimit` tests the effective order (`Model.lean:597-603`); delete the quirk note
(`:45`).

**E6, etcd-range-keys-only-lease** (`txn/range.go:67`): set `FastKeysOnly` false (revert #21791's fast
path), smallest and correct; #22550 (lease in the key index) is upstream's open fix, which a
maintainer objects to. Test (the issue's) must be checked. Risk: keys-only reads go back to reading
values (performance; correctness restored). Spec: `RangeReq.fastKeysOnly` and its lease clause
(`Model.lean:633-646`) deleted; `kv__Get.lean:21`, leasing `Api.lean:159`, snippets
`specreq/txn/read.go:163`, `clientv3kv/ops.go:93` updated.

**E7 + E8, the client's endpoints** (`client/v3/client.go`, `client/v3/internal/resolver/resolver.go`).
E7: a mutex of `EtcdManualResolver`'s own over `endpoints` and `serviceConfig`, taken by `Build`,
`SetEndpoints` and `updateState` (pointer receiver). Not written: the issue's test must be checked
(run under `-race`). E8: `dial` reads `c.endpoints` under `epMu` and returns an error on an empty list.
Not written; `TestStatusEmptyEndpoints`-style test must be checked. Spec: delete `resolverIdle`
(`ApiClient.lean:280-287`), `Client__SetEndpoints.lean`'s premise, `cfgOk`'s `AutoSyncInterval = 0`
(`ApiClient.lean:79-84`), restore `ReqSync`; `epsTok`'s non-empty fraction for `dial`/`Status` becomes an
error disjunct. The resolver is names-only (`Code/.../internal/resolver.toml`): its behavior is a
trusted spec today, so the fix changes a trusted statement (or the package is translated with
bodies: better, it is small).

**E9, etcd-auth-useradd-long-name-fatal** (`server/auth/store.go`): `612320b8e` (an apply-time check,
so a log already holding such an entry restarts); tests pass on the branch (PR text). Spec: W0's
`userAdd`/`roleAdd` step answers the new error for a name over 32768 bytes; `Auth.recordsFit`
(`auth/Api.lean:251-260`) keeps only the record-value half (`nonissues/etcd-auth-record-too-large-
fatal.md`, no test, outside the rule), so `nextOk`'s scope shrinks but stays.

**B1 + B2, bbolt sizes** (bbolt `bucket.go`, `node.go`): `668f5c0` (`Put` rejects a value too large
for its key) and `b71c0a2` (split a node too large for one page); each branch's test fails at
`a4ef197` and passes with its fix (commit messages). Off upstream main, not the fork's `743299d8`:
re-check after the cherry-pick. Spec: `bboltEntryMax` (`Model.lean:136`) and `Put`'s premise
(`Bucket__Put.lean:56`) go, `Put` gains an `ErrValueTooLarge` disjunct for the new bound; `spill`'s
fit argument (`Bucket__spill.lean:7`, `Internal.lean:453`) is re-done for split pages (M). etcd's
backend treats a `Put` error as fatal, so its own size premise (from the request size limit) stays,
now with its source stated at the backend.

**R2, R3, R4, R5** (raft, batched with R1): R2 `validate` (`raft.go`): when both limits are 0, default
`MaxCommittedSizePerReady` to `MaxUint64`-like "one entry" or make `nextCommittedEnts` return at least
one entry; the issue's test must be checked; spec deletes `ConfigOk`'s conjunct (`Api.lean:535`). R3
`15190e3` (raft#547, test `ecb890e` passes on the branch); spec: `InitialState` takes the lock, `memStor`
no longer splits an unlocked share (`Api.lean:95-101`). R4: one field in `Clone`'s literal; spec:
`Config__Clone.lean`'s post. R5: `fd30b41` is documentation only (doc.go, node.go, raft.go comments);
the etcd caller's code fix is already in the fork (`4d9282b0f`), so the raft test then uses raft
against its documented contract and no spec changes; the opt-in guard fix
(`notes/raft-conf-lag-model/guard-fix.md`) is not needed for etcd.

### Off the goal path (briefly)

- **E10** (stop gate, F3): L. The drain premise (`HardStop`/`Stop`'s whole `srvGate`) and `run`'s
  errorc scope (C46) go; every request-path spec gains `ErrStopped`. Needed before any program that
  stops or removes a member while serving. Test `TestV3SerializableReadsOnRemovedMember` must be
  checked; upstream #22190 covers `StorageVersion` only.
- **E11-E14** (mvcc hashing and compaction at 0): cherry-pick #22609 (S; merged upstream, so the
  safest), the `currentRev` read under `s.mu` in `HashByRev` (S), and reject `Compact(rev ≤ 0)` with
  `ErrCompacted` (S: matches W0's model, which already answers `ErrCompacted`; closes E13 and E14 and
  the `compactMainRev = -1` mismatch noted at `EtcdServer__Compact.lean:8-13`). `fix.patch` of E13 is
  the alternative, but leaves `Compact(0)`'s success at a fresh store. Spec: the `rev ≠ 0` scope goes
  from `KV.CompactTriple`, `EtcdServer.Compact`, mvcc's `Compact`; `mvccRestoreGate` stays for
  `HashByRev`'s old-storage read unless `Restore` excludes it in Go too.
- **E15-E21** (watch): E15, E16 (#22295), E18 (`2e9028084`), E21 (`8330458d9`) are small; E17, E19, E20
  are M. Spec gains: `wStep` against `posOf`, no repeated compaction, the wire scope's id clause gone,
  strong `prevOk` (F4), `rev = 0` watches complete from creation (F14), per-call principals for
  v3lock, a realizable `sicEtcdOk`.
- **E22-E28** (streamed range, leases, rafthttp): all S; the lease ones delete C24's `leasePeerURL`
  premise from `TimeToLiveHTTP` (D8's harness question remains for `peerLeaseServed`).
- **C1, L1-L9, K1, K2** (client libraries): branches exist for C1's design (not written), L1-L7, K1,
  K2; L8, L9 not written. With them and the resend fix (F5), leasing meets W0's `KV.*Triple`, which
  deletes the leasing contract's four "does not meet" reasons (`leasing/Api.lean:22-60`) and `lkvMarks`.
- **E29-E32, B5**: no sidestep (liveness, a metric, partial correctness): fix if convenient, no spec
  change required. **B3, B4**: small bbolt fixes deleting C48's second spec and `Prev`'s scope.
- **R6**: the fix is cheap, but the async mode stays outside `ConfigOk`'s scope; no spec change.

## Proposed order

One re-translation per fork per batch; batches 1-2 are the goal path.

1. **Raft batch** (new fork branch on `raft37-goose-lean-a2`): R1 (`raft.go` `newRaft`), R2
   (`raft.go` `validate`/`raft_log.go`), R3 (`storage.go`), R4 (`tracker/tracker.go`), R5 (comments
   only). One `etc/goose.py --project raft`. R1 first: it is the one goal-path premise of the theorem
   and the hardest proof (the new invariant); start its raft-side argument at once (hardest first).
   Optionally R6 (`rawnode.go`) in the same translation, with no spec.
2. **etcd goal batch** (new fork branch on `goose-lean` `a4d2bb172`): `v3rpc/key.go` (E1, E2's count,
   E3) and `v3rpc/codec.go` (E2's size check; toml: translate `codec.Marshal`), `txn/txn.go` (E4),
   `txn/range.go` (E5, E6), `auth/store.go` (E9), `client/v3/client.go` +
   `client/v3/internal/resolver` (E7, E8; toml: the resolver with bodies). One `etc/goose.py --project
   etcd`. Spec order: W0's model first (E3's `putOnce` and `exactFrom` law, E4, E5, E6, E9's error), then
   the server's (E1, E2), then the client's (E7, E8).
3. **bbolt batch**: `bucket.go` (B1), `node.go` (B2), plus B3 (#1305), B4, B5 (`cursor.go`). One
   `etc/goose.py --project bbolt`. B1/B2 are goal: met; B3-B5 ride along.
4. **etcd server batch**: E10 (`server.go`, `v3_server.go`), E11-E14 (`storage/mvcc/kvstore.go`,
   `hash.go`, `etcdserver/v3_server.go` or `mvcc` for the `Compact(≤0)` refusal), E22-E28
   (`v3_server.go`, `lease/leasehttp/http.go`, `rafthttp/util.go`), E29 (`server.go`), E30, E32.
5. **etcd watch batch**: `v3rpc/watch.go` (E18, E19, E17's server half), `mvcc/watchable_store.go`,
   `watcher_group.go` (E15, E16), `client/v3/watch.go` (E17's client half, E31), `v3rpc/interceptor.go`
   (E21), `v3lock`/`v3election` (E20).
6. **etcd client-library batch**: `client/v3/leasing/*` (L1-L9, F5's resend fix), `concurrency`
   (K1, K2), `cache/demux.go` (C1).

Batches 4-6 touch disjoint files and may share one translation if done together.

## `nonissues/` with `blocks-proof: yes` (no fix designs)

"Test?": could a failing Go test be written (the user's rule would then apply).

- `etcd-auth-empty-range-end-point-check`: non-`nil` empty `RangeEnd` checked as one key (A14, C3). Test? yes, through the in-process `v3client` with auth on (gRPC's wire drops the empty bytes).
- `etcd-auth-revision-before-visible`: auth revision bumped before the change is visible (A2, F1). Test? yes, with failpoints between the batch's `Unlock` and the bump.
- `etcd-auth-withroot-token-collision-panic`: two root tokens with one random prefix (F2). Test? hardly: needs a forced collision of a random prefix (no public hook).
- `etcd-backend-name-lost-restart-panic`: first boot's backend name lost at a crash (D7). Test? yes with a crash file system (lazyfs, as etcd's robustness tests); the user accepted the ext4/xfs premise (D7/D31).
- `etcd-member-dir-not-synced`: `member/` never fsynced (D31). Test? as above; accepted premise.
- `etcd-concurrent-remove-last-voter`: two concurrent `RemoveMember`s (F10). Test? yes, an integration test with a failpoint holding the first removal.
- `etcd-lease-keys-mid-apply`: `TimeToLive` keys mid-apply (F11, A18). Test? yes, with a failpoint inside the apply.
- `etcd-merged-snapshot-same-index-image`: two merged snapshots of one index (F9). Test? possible but hard (two merged snapshots at one index in one follower's window).
- `leasing-write-resend-after-error`: a failed write resent lands late (F5). Test? yes, with etcd's integration `bridge` dropping the first reply.
- `k8s-etcd3-watcher-events-after-error`: Kubernetes, no fork. Test? only through a fake watcher today.
- Already fixed on the fork (no action): `etcd-compactor-started-before-start`, `etcd-purge-snapdb-unopened`, `etcd-wal-restart-file-below-snapshot`, `etcd-wal-snapshot-record-order`, `etcd-wal-stale-entries-above-snapshot`, `etcd-watch-resume-stale-canceled-id`, `etcd-watch-resume-nil-watch-chan`, `etcd-watch-resume-waitgroup-overflow`, `etcd-watch-sync-ticker-reset-zero`.


## Added 2026-11-10 (crashreconf test)

- **`etcd-rafthttp-pipeline-process-error-panic`** (goal path: reused peer URLs in `examples/etcd/crashreconf`;
  etcd fork, S): the two-part fix of the issue's `fix.patch` — `writerToResponse.WriteTo` returns
  `error` (so `HTTPError` matches), and `Process` answers a misaddressed message with `412`, not
  `403` (else the latent `nonissues/etcd-rafthttp-misaddressed-403-member-removed.md` becomes real).
  Spec: the rafthttp handlers' status clause (no panic; `403` only for a removed sender).
