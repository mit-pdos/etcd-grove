# Axiom audit (Lean port)

**Started:** 2026-10-18, branch `raft-retarget`. **Why:** the closed adequacy theorem (item 9)
is only as sound as the axioms it rests on, and the trust base (`etc/tcb-baseline.txt`, 327
axioms, 12 `sorry`s) has grown one names-only spec at a time. An axiom here is a claim about Go
code that nobody checked mechanically; a false one can make the closed theorem prove something
false of Go. This file records each axiom's verdict, the reason, and the fix.

**Since phase A:** `membership.localKept` and `localKept_persistent` removed (2026-10-18:
defined from the cluster's lock invariant; their row below). **B4a (2026-10-18):** of
the eight false etcd-internal axioms putget does not reach, four restated true of Go
(`monitorKVHash`, `monitorCompactHash`, `monitorDowngrade` restricted to the configuration that
turns them off; `SetVersionChangedNotifier` with its field owned), four stopped for a decision
(D19m: `revokeExpiredLeases`, `Cleanup`, `createMergedSnapshotMessage`, `mvcc.store.Close`); no
axiom added or removed.

## Phase A result (2026-10-18)

All 330 axioms (the baseline's 327 and point 5's three) have a verdict in the table below:
**39 false, 7 suspect, 222 ok, 62 benign** (B1 found two of the ok ones false, the
`dialWithBalancer` pair: 41 and 220). Of the false ones, 11 are premise gaps (an argument
every caller already gets right) and 12 are latent (no proof uses the failing instance). The
false axioms, most important for putget (`examples/putget`, item 9) first:

1. **`convert_float64_to_int64`: inconsistent in Lean. Fixed (B1, 2026-10-18).** It was stated
   for every `GoLocalContext`, and Perennial's default instance (`is_go_step_pure := fun _ _ _ =>
   False`) gives `False` from it in any proof context (checked in Lean, and `False` closed from
   concrete instances of every class). Now the hypothesis class `Float64ToInt64Semantics`, which
   `NewServer.wp_proof` and `wp_NewServer` take as `go.Semantics` is taken. The same check found
   two more inconsistent axioms of the same kind, also fixed: `Client.dialWithBalancer.unfold`
   and `.builderType` (now the class `DialWithBalancerBody`). Every other axiom quantified over
   the semantics' parameters was checked: none states a step, unfolding or type fact
   (`notes/decisions.md`, "`int64(f)`: a hypothesis class").
2. **`EtcdServer.monitorStorageVersion`: reached in putget's own Go run.** Once the cluster
   version is set, it migrates the storage version, writing the backend's `meta` bucket under the
   batch lock, which the apply thread owns. **B2 (2026-10-18): stopped, D19i** (the migration
   breaks the backend model's duplicate-put premise, a Go stale read confirmed at the pin). **D19i part 2 (2026-10-18):** the fix in the fork, the premise gone; restated with the
   backend's write access and the shared write budget (D19i (i)).
3. **`EtcdServer.snapshot`, `EtcdServer.compactRaftLog`** (points 2 and 1, confirmed). They change
   raft's `MemoryStorage` (and the WAL) without `ownMemoryStorage`/`memSnapTok`. They run every
   `memorySnapshotCount = 100` applied entries, not 10000: within the model's reach, though
   putget's run applies only a handful. **B2 (2026-10-18): stopped, D19i** (raft's storage
   contract must admit a boundary the application raises). **D19i part 1 (2026-10-18): stopped
   before any Lean change**: raft's bound is `raftLog.applied`, and etcd compacts past it between
   `notifyc` and `Advance` (`issues/etcd-compact-past-raft-applied.md`); a fork fix to choose
   (D19i (A1)/(A2)).
4. **`storage.NewBackendQuota`, `EtcdServer.Alarm`, `EtcdServer.raftRequestAlarm`**: on the
   `Put` path. `NewBackendQuota` assumes the backend never reaches its quota without saying so.
   The two alarm contracts propose a NOSPACE alarm, which is not `plainReq`, so the KV model
   excludes it. In putget's run the 2 GiB quota is never reached. **B3 (2026-10-18), D19h
   option (B):** `NewBackendQuota` fixed (under the named workload premise
   `apply.backendUnderQuota`, threaded to `NewServer.spec` and `v3rpc.Server`); `EtcdServer.Alarm`
   gone (its branch dead); `raftRequestAlarm` still false (its branch's deadness needs the
   answers' errors: D19h). **The unit, stopped (2026-10-18), D19k:** the dead branch needs the
   error variables' pointers told apart, which no fact gives (option (A): `errors.New`'s field in
   the init facts, a `gen-init.py` change).
5. **`EtcdServer.applyConfChange`**: stated for every change. It applies the change to raft
   without `node.ApplyConfChange`'s premise, panics on malformed contexts, and can remove the
   local member, against `localKept`. It is reached at bootstrap with `AddNode(self)`, an instance
   that is plausibly true. **Fixed (B3, 2026-10-18):** restated for the changes the server's
   policy admits (`ccApplyOk`), through the raft node's contract (`raftPropose`'s
   `ApplyConfChange`, proved from `node.ApplyConfChange`).
6. Not reached by putget:
   - `EtcdServer.revokeExpiredLeases`: proposes `LeaseRevoke`.
   - `Cleanup`: closes the backend and the KV.
   - `createMergedSnapshotMessage`
   - `monitorKVHash`, `monitorCompactHash`, `monitorDowngrade`: propose alarms or downgrade
     changes once their configuration enables them.
   - `mvcc.store.Close`: keeps `schedLive`.
   - `RaftCluster.SetVersionChangedNotifier`: an unlocked write.
7. Latent:
   - `time.Since`: assumes a positive result (known, filed).
   - `grpc.ClientConn.NewStream`: a retrying server stream.
   - The four prometheus `WithLabelValues`/`With`: label count and UTF-8.
   - bbolt's `wBkt`/`wBkt_persistent`/`DeleteBucket_kv`, `Cursor_kvw`, `DB.Info_kv`.
   - `auth.authStore.AuthInfoFromTLS` (known, filed).
8. Premise gaps:
   - `strconv.FormatUint`
   - `mvcc.store.restore`
   - `lease.lessor.Promote`
   - `addFeatureGateMetrics`
   - `monitorFileDescriptor`
   - `mvcc.hashStorage.Store`
   - `kvHasher.WriteKeyValue`, `kvHasher.Hash`
   - `BackendQuota.Cost`
   - `txn.WarnOfExpensiveRequest`, `txn.WarnOfFailedRequest`

Suspects:

- `publishV3` and `monitorClusterVersions`: D19c's restriction of what they propose holds, but
  `raftRequest`'s reader slots are not in their preconditions.
- `sendMergedSnap`: unowned state.
- `grpc.serve`: at most `n` concurrent handlers.
- `grpc.serveStream`: at most `n` Watch streams per run. This one matters for long runs.
- `errors.IsCtxErr`: any error's `Is` method.
- `proto.Marshal`: unknown fields, and the `state'` cell.

The predicate families (bbolt/backend, gRPC) have models, sketched in their sections.

No new Go bug was found. The two Go issues the table cites were already filed:
`issues/etcd-watch-sync-ticker-reset-zero.md` and `issues/etcd-auth-tls-info-assert.md`.

## Verdicts

- **false**: the spec claims something the Go code does not do. Typically the code writes state
  that the spec frames out (state other resources own), or it panics or blocks where the spec
  says it returns. A false axiom is unsound, not just unproved.
- **suspect**: not shown false, but its argument needs checking. Examples: a proposal to raft
  that the spec does not restrict, a set of predicate laws with no model, a claim about another
  process.
- **ok**: the spec checked against the Go body (or the library's documented behavior) and holds.
- **benign**: a library spec whose content is trivially true or whose only effect is logging,
  formatting or metrics, with no ownership of shared state.

## Method

For each axiom: read the Go body at the pinned revision (`.lake/go-src/etcd/...`,
`.lake/go-src/raft/...`, or the library's source), list the state it reads and writes and the
calls it makes (including proposals to raft and sends on channels), and compare with what the
spec's precondition owns and its postcondition gives back. An axiomatized predicate's laws
(persistent, timeless, fractional, ...) must have a model: some interpretation in which every
law of that family holds at once.

## Known or likely problems (2026-10-18)

1. **`EtcdServer.compactRaftLog`: false.** The spec is `{srvLgReader s} … {srvLgReader s}`.
   The Go code (`server/etcdserver/server.go`, `compactRaftLog`) calls
   `s.r.raftStorage.Compact(compacti)`, which rewrites the `MemoryStorage`'s entries. The
   model gives those to raft's node goroutine (`ownMemoryStorage`), so the triple is false in
   the model. It runs once etcd's snapshot count of applied entries is reached, within the
   closed theorem's step bound.
2. **`EtcdServer.snapshot`: false.** The Go code calls `s.KV().Commit()`,
   `s.r.raftStorage.CreateSnapshot(...)` and `s.r.storage.SaveSnap(...)`; the spec owns none
   of the storage. Since D17d (`rnSnapOnce`), `MemoryStorage.CreateSnapshot` takes the
   application's snapshot token `memSnapTok`, which this spec does not take.
3. **Unchecked, same pattern possible:** `EtcdServer.applyConfChange` (frames only the conf
   change and `ep`'s conf state), `createMergedSnapshotMessage`, `sendMergedSnap`,
   `revokeExpiredLeases`, `raftRequestAlarm`, `Cleanup`, `stopWithDelay`, and `Start`'s
   monitors (`adjustTicks`, `purgeFile`, `monitorFileDescriptor`, `monitorStorageVersion`,
   `monitorKVHash`, `monitorCompactHash`, `monitorDowngrade`). A method that proposes to raft
   must be restricted in what it proposes, or the KV workload invariant (`kvInv`,
   `clusterWorkloadOk`) can break. D19c did this (`srvMonitorPermit`) for `publishV3` and
   `monitorClusterVersions` only.
4. **Large models, suspect until a model is shown:** bbolt's `*_kv` triples and the `backend.*`
   predicates with their laws (about 65); gRPC's serving and client axioms with their
   predicates (about 50). The risk is a family of laws that no model satisfies at once, which
   would let a proof derive `False`.
5. **Not yet in the baseline:** `EtcdGrove.goose_adequacy_start` (D19d),
   `EtcdGrove.initLb_of_spec` (D19e), `features.NewDefaultServerFeatureGate` (item 9 point 7;
   its predicate `isFeatureGate` was false of Go until 2026-10-18). No linked result reaches
   them yet; `Main`'s proof will.

## Plan

- **Phase A (read-only; started 2026-10-18):** a verdict for every axiom in
  `etc/tcb-baseline.txt` and the three of point 5, grouped by package in the table below, with
  the reason for each one that is not **benign**. Go bugs found on the way go in `issues/`.
- **Phase B (after `rnLogFits` and the `NewServer.spec` round, D19g, land):** fix the **false**
  axioms by giving each spec the resources its Go code touches, as D17d did for `Snapshot()`.
  For example, `MemoryStorage.Compact`/`CreateSnapshot` under the lock with the application's
  token, and a proposal permit for the methods that propose. Then re-prove the callers.
  **Order (adopted by the user, 2026-10-18):** B1 `convert_float64_to_int64` (inconsistent;
  started at once, not waiting for D19g); B2 `monitorStorageVersion`, `snapshot`,
  `compactRaftLog` (the backend's batch lock, raft's storage token); B3 the alarm/quota path
  (`NewBackendQuota`, `Alarm`, `raftRequestAlarm`) and `applyConfChange` (restricted to what
  putget reaches, or a permit); B4 the false axioms putget does not reach, then the latent ones
  and the premise gaps.
- **Phase C:** models for the **suspect** predicate families (bbolt/backend, gRPC), or a
  narrower set of laws.

## Table

Verdicts are for the instances the proofs use. **A caveat common to the names-only contracts** whose
precondition is only `isPkgInit` (`∀ s, {{ isPkgInit }} s.m(…) {{ True }}`): read literally they
are false for an `s` that is not a live server (the Go body dereferences `s`); no proof
instantiates them so, and the rows below do not count it. A missing premise on another argument
(a nil logger, a malformed key) that every caller meets is recorded as **false (premise gap)**:
literally false, harmless at every call site, fixed by stating the premise.

### `etcdserver` (`EtcdServer.*`, the names-only methods; Go: `server/etcdserver/server.go` unless
named; specs: `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__<m>.lean`)

| axiom | verdict | reason |
|---|---|---|
| `EtcdServer.compactRaftLog` | **false** | Point 1 confirmed. `compactRaftLog` (2132) calls `s.r.raftStorage.Compact(compacti)`, whose spec (`Spec/go_etcd_io/raft/v3/MemoryStorage__Compact.lean`) needs raft's `ownMemoryStorage` with nothing pending; the contract owns only `srvLgReader s`. Reached much earlier than point 1 said: `snapshotIfNeededAndCompactRaftLog` (1210) runs it whenever `shouldSnapshotToMemory` holds, i.e. every `memorySnapshotCount = 100` applied entries (116), not only at `SnapshotCount = 10000`. Go itself is fine (the storage's mutex); the model is wrong. **B2 (2026-10-18): not fixed, needs a decision (D19i).** No true restatement exists over the current model: raft's view of the storage is exact (`MemView`, `isStorage`'s `FirstIndex`, `ownRaftLog`'s `LogStoreOk`), so a compaction the application makes concurrently needs raft's storage contract to take a rising boundary (D19i (A)). **D19i part 1 (2026-10-18): stopped, needs a decision.** Worse than a model gap: raft needs the boundary at most `raftLog.applied` (`hasUnappliedConfChanges`), which `Advance` moves after `notifyc`, and `compacti = appliedi - SnapshotCatchUpEntries` exceeds it in that window when one `Ready` carried more than `SnapshotCatchUpEntries` committed entries: raft can panic (`issues/etcd-compact-past-raft-applied.md`, reproduced on raft). A true restatement needs an etcd fix first (D19i (A1)/(A2)). |
| `EtcdServer.snapshot` | **false** | Point 2 confirmed. `snapshot` (2078) calls `s.r.raftStorage.CreateSnapshot(ep.appliedi, ep.confState, nil)`, whose spec needs `ownMemoryStorage` (nothing pending) and since D17d `memSnapTok`; with `toDisk` it also writes the WAL and the snapshotter (`s.r.storage.SaveSnap`, `Release`), which the raft loop writes concurrently. The contract owns none of them. Reached with `compactRaftLog` (every 100 applied entries). `KV().Commit()` is covered by `applyBackend`/`srvApplyKV`. **B2 (2026-10-18): not fixed, needs a decision (D19i).** D17d's token lets the application read the snapshot, not write it: `memSnap_update` needs the owner's part too. The WAL's `SaveSnap`/`Release` are not the obstacle (the WAL's model is stateless). **D19i part 1 (2026-10-18): stopped** with `compactRaftLog` (D19i (A1)/(A2)); under (A1) the snapshot is taken after raft's `Advance` and is bounded by the same published `applied`. |
| `EtcdServer.applyConfChange` | **false** (as stated); **fixed (B3)** | For every change `m`: (a) it calls `s.r.ApplyConfChange(cc)` (2008, 2022), i.e. raft's `node.ApplyConfChange`, whose spec (`Spec/go_etcd_io/raft/v3/node__ApplyConfChange.lean`) needs `CCShrink` in the static mode or `DynCCPreOp`, and raft's `isNode`; the contract asks for neither, so it changes raft's configuration outside raft's proof; (b) it panics (`lg.Panic`, here and in `membership.ValidateConfigurationChange`, `cluster.go:321,377,386`) on a context that is not the JSON of a member or an unknown type, which the contract does not exclude; (c) `RemoveNode` of the local member deletes it from `c.members` (`RemoveMember`), contradicting the persistent `membership.localKept`. Reached in putget: the bootstrap's `AddNode(self)` entry (validation passes, `membersFromBackend` is empty on a new backend; `AddMember` rewrites the member, no `AddPeer`); that instance is plausibly true (a change raft already applied at `Bootstrap`), so the fix is to restrict `m` (to `CCShrink` and well-formed contexts, as `node.ApplyConfChange` does). **Fixed (B3, 2026-10-18):** the spec takes a change `ccApplyOk` at raft's configuration (an `AddNode` of a member of the configuration whose context unmarshals, `membership.ccContextOf`, opaque, to that member, not a promotion: no panic, no removal) and the server's raft node `srvRaftNode` (now in `isServer`), whose `raftPropose` gained `ApplyConfChange` for a change `ccRaftOk` admits (an `AddNode` of a voter or of node `0`), proved from `node.ApplyConfChange.spec` in the static mode (`ccShrink_of_raftOk`); the change goes to raft read-only (`DFrac.discard` in the post). The call site discharges `ccApplyOk` from `entryWaitOk`, which the KV invariant's `kvWork` (`ccLogOk`) and `srvCCPolicy` (`ccBootOk`) now carry. Still an axiom (names-only), restated. |
| `EtcdServer.createMergedSnapshotMessage` | **false** | `snapshot_merge.go:32` commits the backend (`s.KV().Commit()`), takes a backend snapshot (`s.be.Snapshot()`, a bbolt read transaction streamed by a goroutine), reads `*confState` (`proto.Clone`) and writes `m.Snapshot`; the contract owns no backend, no `m` (the `msgSnapC` bag's predicate gives none) and no `cs`. Only on a leader with a follower that needs a snapshot: not reached in single-member putget. **B4a (2026-10-18): stopped, needs a decision (D19m)**: the receive from `msgSnapC` is dead in a single-member cluster, but showing it needs raft's messages addressed to other voters and the configuration kept `{self}` (D19m (A)). |
| `EtcdServer.sendMergedSnap` | suspect | Writes `s.inflightSnapshots` (an atomic that `compactRaftLog` reads), hands `merged` to `s.r.transport.SendSnapshot`, and `GoAttach`es a goroutine; nothing in the model owns these, so it is sound only while nothing does. Not reached in putget (no `MsgSnap`). |
| `EtcdServer.revokeExpiredLeases` | **false** (as stated) | For a non-empty `leases` (854) its goroutine proposes `LeaseRevoke` through `s.LeaseRevoke`→`raftRequest` with no `reqPropOk` (a revoke deletes the lease's keys: the KV workload invariant can break) and calls `ensureLeadership` (`s.read.LinearizableReadNotify`); the contract takes nothing. Not reached in putget's Go execution (no lease is granted, so `ExpiredLeasesC` never fires), but `run`'s proof uses it for every `leases`. **B4a (2026-10-18): stopped, needs a decision (D19m)**: no lease ever exists in the model (`plainReq` excludes `leaseGrant` and leased puts, the lease bucket is fresh), so `expiredC`'s receive is dead, but the lessor's contract gives its bag the predicate `True`; options: the lessor's granted set in the model (recommended), a workload premise, or leases in the KV model. |
| `EtcdServer.raftRequestAlarm` (`AlarmContract.lean`) | **false** | A second contract of the *verified* `raftRequest` for **every** `InternalRaftRequest` `v` (`p ↦ v`), with no `reqPropOk`, id credit or reader slots: it lets a proof propose a `Put`/`Txn` outside the KV workload invariant. Even the one use (`applyEntryNormal`'s NOSPACE goroutine, `{Alarm: {ACTIVATE, NOSPACE}}`) is outside the model: an alarm request is not `plainReq` (`KVModelDefs.lean:63`, "alarm requests … depend on stores the model treats as oracles"), and a committed NOSPACE alarm switches the applier chain to the capped one, which rejects later puts whose persistent atomic update already fired at commit. In Go it needs the backend over its quota (`ErrNoSpace` from the applier): not in putget (2 GiB default), but the model's quota is an oracle. Fix: model the alarm (the chain's `kvExact` after a NOSPACE alarm) or exclude it by a quota argument. **Still false after B3 (2026-10-18):** under `backendUnderQuota` Go never takes `applyEntryNormal`'s branch, but the model cannot show it yet (the answers' errors, `errors.Is`, the alarm store as an oracle): the unit is in D19h. **Unit stopped (2026-10-18), D19k:** with the workload narrowed to the proposers' kinds and the start's chain, `ar.Err` is `nil` or a backend error (`ErrKeyNotFound`, `ErrLeaseNotFound`, `ErrFutureRev`, `ErrCompacted`), but no fact says those variables' pointers differ from `ErrNoSpace`'s, so `errors.Is` cannot be shown `false`. Options in D19k; recommended (A), `errors.New`'s `s` cell in the init facts. |
| `EtcdServer.monitorStorageVersion` | **false** | Its monitor (`version/monitor.go:108`) calls `UpdateStorageVersion` (`adapters.go`): `s.be.BatchTx()` with `LockOutsideApply`, then `schema.UnsafeMigrate`, which writes the meta bucket's `storageVersion` (`migration.go:101`); the backend and its batch lock are the apply thread's (`applyBackend`, `batchLockInv`). **Reached in putget**: once `monitorClusterVersions` sets the cluster version (3.7; `firstCommitInTerm` fires at the leader's first commit) the storage version is detected as 3.5 (no `storageVersion`, term > 0: `UnsafeDetectSchemaVersion`) and migrated, on `clusterVersionChanged` or after 4 s. **B2 (2026-10-18): not fixed, needs a decision (D19i).** The model does admit a write under `LockOutsideApply`, but the migration puts `meta/storageVersion` three times in one session, which `UnsafePut`'s `wbDupOk` excludes; in Go a `ReadTx` then reads the oldest value (confirmed at the pin: `issues/etcd-backend-duplicate-put-stale-read.md`, "An etcd caller"). **D19i part 2 (2026-10-18): restated, true as far as the backend goes.** The Go fix (etcd-io/etcd#21987) in the fork (`ea78ec948`), the backend's premise gone; the contract takes `srvSVRes` (the backend for good, its contract, a read token with an open share, `bemu`/`lgMu` slots) and the write budget `srvWTPool` shared with the apply thread, threaded from `NewServer` through `Start` (D19i (i)). Its reads of the cluster, `clusterVersionChanged`, `stopping` and the WAL are not in it (as `monitorClusterVersions`: minor). |
| `EtcdServer.monitorKVHash` | **false** (as stated) | With `CorruptCheckTime ≠ 0` it reads the whole backend (`VerifyBackendConsistency`, `PeriodicCheck`'s `HashByRev`) and on a mismatch proposes `Alarm{CORRUPT}` through `raftRequest` (`corrupt.go`, `TriggerCorruptAlarm`), none of it owned or permitted. Returns at once in putget (`CorruptCheckTime = 0`, 2246). **Fixed (B4a, 2026-10-18):** the contract takes `s.Cfg.CorruptCheckTime ↦□ 0`, under which the body returns at once (`srvMonitorsOff`, `NewServer`'s `srvMonitorCfg`; D19m). Still an axiom (names-only), restated. |
| `EtcdServer.monitorCompactHash` | **false** (as stated) | With the `CompactHashCheck` feature on, `CompactHashCheck` reads the store's hashes and may propose `Alarm{CORRUPT}`; nothing owned or permitted. Returns at once in putget (the feature is off by default, 2276). **Fixed (B4a, 2026-10-18):** the contract takes the feature gate field and `featureIs fg "CompactHashCheck" false` (the gate's new persistent fact, which `NewDefaultServerFeatureGate`'s spec returns: the feature's default), under which it returns at once (D19m). Still an axiom (names-only), restated. |
| `EtcdServer.monitorDowngrade` | **false** (as stated) | With `DowngradeCheckTime ≠ 0` and a downgrade enabled, `CancelDowngradeIfNeeded` proposes `DowngradeInfoSet` (`adapters.go`, `DowngradeCancel`) without a permit (not in `monitorReq`). Returns at once in putget (`DowngradeCheckTime = 0`, 2336). **Fixed (B4a, 2026-10-18):** the contract takes `s.Cfg.DowngradeCheckTime ↦□ 0` and, for its `NewMonitor(s.Logger(), …)` before the check, an `lgMu` reader slot and the logger field (D19m). Still an axiom (names-only), restated. |
| `EtcdServer.publishV3` | suspect (minor) | D19c's restriction holds: it proposes only `ClusterMemberAttrSet` (1793). But `raftRequest`'s spec also needs a reader slot of `leadTimeMu` (`srvLeadTimeReader`, an `ownRWMutex`), the auth reader `E.RD` and `mvcc.idxCert`, which the persistent `srvMonitorPermit` does not give; true of Go (a read lock) only if the model can mint such slots freely. It also closes `s.readych` (no owner in the model). |
| `EtcdServer.monitorClusterVersions` | suspect (minor) | As `publishV3`: it proposes only `ClusterVersionSet` of a parsed `semver` (`updateClusterVersionV3`, through `GoAttach`), but the reader slots are not in its precondition. It also reads `s.cluster` and asks the peers' versions over HTTP (`getMembersVersions`). |
| `EtcdServer.adjustTicks` | ok | Reads `s.cluster.Members()` under the cluster's mutex and the transport's active peers, and calls `s.r.advanceTicks` (single member: `ElectionTicks − 1` ticks), whose proof takes only the persistent `isRaftNode` (each tick's credit from a time receipt). Waits at most `ConnReadTimeout`. |
| `EtcdServer.purgeFile` | ok | Removes old `*.snap.db` files in the snap directory (not the backend's `db`) and, with `MaxWALFiles > 0`, old WAL files; `lg.Fatal` on an error (diverges). No state the model owns. |
| `EtcdServer.stopWithDelay` | ok | Waits, then a non-blocking send on `s.errorc`, a bag with a trivial predicate (`InvRun.lean`). |
| `EtcdServer.Cleanup` | **false** (as stated) | Stops the lessor and compactor and closes the KV, the auth store and the backend (`be.Close` commits the batch transaction and closes bbolt), which the model's invariants keep describing as live; request goroutines (not in `s.wg`) can still use them. Only on `run`'s shutdown, which putget never reaches. **B4a (2026-10-18): stopped, needs a decision (D19m)**: `run`'s exits (`s.stop`, `s.errorc`) dead in the runs covered (recommended for the closed theorem), a "server open" token threaded through the request paths, or closed states in the stores' models. |
| `EtcdServer.Alarm` (`v3_server.go:805`) | **false** | `raftRequest` with `{Alarm: r}` (the type assertion holds); the precondition is `raftRequest`'s without `reqPropOk`, and `reqPropOk` cannot hold for it: an alarm is not `plainReq` (`KVModelDefs.lean:63`), the KV model's condition on every proposal (see `raftRequestAlarm`). **On putget's proof path**: `quotaAlarmer.check` (verified, `quotaAlarmer__check.lean`), which every `Put` goes through, calls it when the quota's `Available` answers false, which the model leaves open. Not reached in putget's Go execution (one small key against a 2 GiB quota). Same fix as `raftRequestAlarm`. **Removed (B3, 2026-10-18):** under `backendUnderQuota` `quotaAlarmer.check`'s alarm branch is dead; the spec, the axiom and its link entry are gone. |
| `EtcdServer.IsLearner` | ok | `IsLocalMemberLearner` (`cluster.go:786`) under the cluster mutex; its panic is excluded by `membership.localKept`, since 2026-10-18 the lock invariant's `rcLocalIn` (the members map has `c.localID`). |
| `EtcdServer.IsMemberExist` | ok | A map lookup under the cluster mutex (`cluster.go:823`). |

### bbolt and the backend's bbolt layer (70; Go: `go.etcd.io/bbolt@v1.5.0`, `server/storage/backend/`; Lean: `Proof/go_etcd_io/etcd/server/v3/storage/backend/{InvBbolt,BboltOptions,BboltOptsDefs,MutexLit}.lean`, `Spec/go_etcd_io/bbolt/`)

The predicate family has a model in which every law holds at once, except the two latent
`false` rows (the handle of a deleted bucket; a write transaction's cursor):
`ownDB` the full authority over the committed data, `wrTok` an exclusive token, `isDB db` the pure
fact "`db` came from `Open`" (still true after `Close`), `fileHolds` the file's FFI state; each
transaction a byte region `R_tx` (its mmap pages, and for a writer its nodes and cloned keys) in a
ghost map, `txLive tx q := ⌜tx ≠ null⌝ ∗` `R_tx` at fraction `q`, `txBytes tx s b` the persistent
fact `s ⊆ R_tx` holding `b` (true of Go: a reader holds `mmaplock.RLock`, and a writer's `node.put`
replaces slice headers, never bytes); `rtxSnap`/`rBkt` persistent facts of a reader's fixed
snapshot, `rtxStats` an exclusive per-transaction token; `ownWTx` the writer's authority `●S ∗
txLive tx 1 ∗` the `FillPercent` cells of the handles given out; `txDone`/`txDB` persistent facts
recorded at commit/rollback and at `Begin`.

| axiom | verdict | reason |
|---|---|---|
| `backend.wBkt`, `wBkt_persistent`, `bbolt.Tx.DeleteBucket_kv` (3) | **false** (latent) | `wBkt tx b n` is persistent and outlives `DeleteBucket(n)`; after `CreateBucketIfNotExists(n)` the specs allow `Put_kv`/`Delete_kv`/`Cursor_kvw` through the old handle `b`, but Go's `DeleteBucket` (`bucket.go:316-322`) sets that handle's `nodes = nil` and a later `Put` panics at `common.Assert(b.nodes != nil)` (`bucket.go:864`). No proof does this (etcd's `batchTx` fetches the bucket per operation). Fix: `DeleteBucket` consumes `wBkt` for `n`, or `wBkt` carries a generation `ownWTx` agrees with. |
| `bbolt.Bucket.Cursor_kvw` (1) | **false** (latent) | A write transaction's cursor gets `ownCur tx c (bktEnts m) none`, frozen at `m`, and `Seek_kv`/`Next_kv` need only `txLive`; after a `Put_kv` on the bucket the specs say `Seek` returns the old entries, while Go's `Cursor.seek` reads the materialized nodes and sees the new one (empty bucket, `Cursor`, `Put "a"`, `Seek "a"`: spec nil, Go `"a"`). Unused so (`batchTx__UnsafeRange.lean` uses a cursor within one call). Fix: write-transaction `Seek`/`Next` read `ownWTx`'s `S`, or `Put`/`Delete` take the cursor back. |
| `bbolt.DB.Info_kv` (1) | **false** (latent) | Needs only the persistent `isDB db`, true after `Close_kv`; Go's `DB.Info` (`db.go:1124`) asserts `db.data != nil` (a panic after `Close`) and reads it without `mmaplock`. The one caller, `backend.begin` (`backend.go:1095`), holds a live transaction, so the instance used holds. Fix: require `txDB tx db ∗ txLive tx q`. |
| `backend.ValidateCalledInsideApply`, `ValidateCalledInsideUnittest`, `ValidateCalledOutSideApply`, `VerifyBackendConsistency` (4) | ok (assumption) | `storage/backend/verify.go:31-91`: no-ops unless the environment variable `ETCD_VERIFY` is `lock`/`all`; with it set they panic (`lg.Panic`/`lg.Fatal`) from the wrong goroutine or on a mismatch. A deployment assumption (`ETCD_VERIFY` unset) the closed theorem's statement does not show. |
| `backend.newBoltLoggerZap` (1) | ok | `backend.go:1135`, a non-nil logger wrapped. |
| `backend.boltLogger`, `boltLogger_persistent` (2) | ok | Model: a pure fact (`l` a `*zapBoltLogger`). |
| `backend.optsAt`, `optsVal`, `optsAt_discard_persistent`, `optsAt_bool`, `optsAt_int`, `optsAt_freelist`, `optsAt_timeout`, `optsAt_logger` (8) | ok | Model: `optsAt l dq o := ∃ v, l ↦{dq} v ∗ ⌜optsVal v o⌝`; the fields match `bbolt@v1.5.0/db.go`'s `Options`. |
| `backend.wp_optsLit`, `wp_optsAlloc`, `wp_optsLoad`, `wp_optsStore`, `wp_mutexLit` (5) | ok | Semantic rules for types Goose does not translate (`bolt.Options{}` the zero value, `sync.Mutex{}` unlocked); `go.Semantics` is an open class, so they add true rules rather than contradict a step relation. |
| `backend.ownDB`, `wrTok`, `isDB`, `isDB_persistent`, `fileHolds` (5) | ok | Model above. `fileHolds` has no introduction law: the closed theorem must assume it for `backend.New`'s file. |
| `backend.txLive`, `txLive_fractional`, `txLive_nonnull`, `txLive_timeless`, `txBytes`, `txBytes_persistent`, `txBytes_acc` (7) | ok | Model above; `R_tx` grows only under `txLive 1`, and `Commit`/`Rollback` need `txLive 1` back. |
| `backend.rtxSnap`, `rtxSnap_persistent`, `rtxStats`, `rtxStats_excl`, `rtxStats_timeless`, `rBkt`, `rBkt_persistent`, `rBkt_timeless` (8) | ok | Model above (bbolt v1.5 read transactions cache no child buckets; stats are atomic). |
| `backend.ownWTx`, `ownWTx_live`, `ownWTx_fill`, `backend.ownCur` (4) | ok | Model above; `ownCur` an exclusive cursor ownership. |
| `backend.txDone`, `txDone_persistent`, `txDB`, `txDB_persistent` (4) | ok | Model above; `Tx.DB_kv` also needs `txLive`, so Go's `tx.db = nil` at close is not observed. |
| `bbolt.Bucket.Cursor_kvr`, `Cursor.Next_kv`, `Cursor.Seek_kv`, `Tx.Bucket_kvr`, `Tx.Rollback_kv` (5) | ok | `cursor.go`, `bucket.go:74-110`: `Seek` the first key ≥ the sought one (bytewise), `Next` past the end `nil, nil`, `Bucket` nil when absent. |
| `bbolt.DB.Begin_kv`, `Tx.Commit_kv` (2) | ok | Errors in the error disjunct; blocking on `rwlock`/`mmaplock` is allowed (partial correctness); a failed commit gives back only `txDone` (weak, sound). |
| `bbolt.Bucket.Put_kv`, `Bucket.Delete_kv`, `Tx.CreateBucketIfNotExists_kv`, `Tx.Bucket_kvw` (4) | ok | `bucket.go:205-265, 452-534`: the error branches are excluded by the premises (live writable transaction, key length in `(0, 32768]`, value below `MaxValueSize`, no nested buckets). |
| `bbolt.Open_kv` (1) | ok | Needs `o.ok` (not read-only, page size 0, no `OpenFile`), consumes `fileHolds`; errors allowed. |
| `bbolt.DB.Close_kv` (1) | ok | `db.go:694` takes `rwlock`, `metalock`, `mmaplock` exclusively, so no live transaction reads unmapped memory after it. |
| `bbolt.DB.Stats_kv`, `Tx.Size_kv`, `Tx.Stats_kv`, `Tx.DB_kv` (4) | benign | Read-only accessors. |

### Library specs (90: zap, fmt, time, strconv, context, errors, proto, semver, heap, sort, rand, reflect, strings, math, utf8, humanize, otel, types, verify, version, enum `String`s, `DescribeConfChange`; specs under `Spec/<pkg>/`)

| axiom | verdict | reason |
|---|---|---|
| `time.Since` | **false** (known) | `Spec/time/Since.lean` gives `0 < d`, an assumption the file states; Go returns 0 when the monotonic clock did not advance (coarse clocks, e.g. Windows) and can return a negative duration for a `t` without a monotonic reading. With 0, `syncWatchersLoop`'s `delayTicker.Reset(syncDuration)` panics (`watchable_store.go:240-246`; `issues/etcd-watch-sync-ticker-reset-zero.md`, upstream etcd-io/etcd#22296). The branch needs unsynced watchers: not taken in putget (no watch). |
| `strconv.FormatUint` | **false** (harmless) | No premise on `base`; Go panics outside 2..36 (`internal/strconv/itoa.go`). The one caller (`read.go:131`) passes 10. Fix: `2 ≤ base ≤ 36`. |
| `errors.IsCtxErr` | suspect | The premise `context.isTypedErr err` only says the type implements `error`; `errors.Is` calls the error's own `Is`/`Unwrap`, arbitrary code. Callers pass `context.Canceled`/`DeadlineExceeded`, for which it holds. Fix: take `ErrDone`'s disjunction as the premise. |
| `proto.Marshal` (`KeyValue`) | suspect (low) | `x`'s unknown fields are unconstrained (Go appends them, so the bytes are not `kvEncode kv`), and the post keeps `state'` though `ProtoReflect` stores the message info there. Every caller marshals a fresh `KeyValue`. Fix: premise `unknownFields' = nil`, an existential `state'`. |
| `zap.Logger.Fatal` | ok | Post `False`: `logger.go:350` always exits (`WriteThenFatal`, even on a nop core). Its comment ("no verified function reaches it") is stale: the backend's proofs call it. |
| `zap.Logger.Panic` | ok | `panic(ce.Message)` whatever the core (`zapcore/entry.go:196`); the spec's `PanicV #msg` is the bare string, which matters only to a `recover` that inspects it. |
| `zap.Logger.Debug`/`Info`/`Warn`/`Error` (4) | ok | Log only; etcd never sets `Development`, a panic hook or a fatal hook, so no `DPanic`. |
| zap field constructors (`ByteString`, `Duration`, `Error`, `Int'`, `Int32`, `Int64`, `Stack`, `String`, `Stringer`, `Uint`, `Uint32`, `Uint64`) (12), `zap.NewNop` | benign | Values only. |
| `fmt.Errorf`, `fmt.Printf` (2) | ok | `argsOk` asks each argument's `Error()`/`String()` for a spec; `Formatter`/`GoStringer` arguments are not excluded but no caller passes one. |
| `fmt.SprintfClientPtr`, `fmt.SprintfNamed` (2) | ok | `*clientv3.Client` and `LeaseID` have no `String`/`Error`/`Format` method. |
| `fmt.Sscanf` | ok | Matches `fmt/scan.go`'s `%d` path. |
| `time.NewTicker`, `Ticker.Reset`, `Ticker.Stop` (3) | ok | A positive period required (Go panics otherwise); ticks over-approximated. |
| `time.Duration.Seconds`, `Seconds_ptr`, `Duration.String`, `Time.After`, `Time.IsZero`, `Time.Unix` (6), `strconv.FormatBool` | benign | Values only. |
| `context.Err`, `ErrDone`, `ValueStartTime`, `WithCancelTodo`, `WithCancelValCtx`, `WithTimeoutBackground`, `WithValue` (7) | ok | Checked against `context.go`; `ValueStartTime` is a closed-world fact true of etcd (only `v3_server.go:302,374` store `StartTimeKey`, with `time.Now()`). |
| `errors.IsDeadlineExceeded`, `errors.IsStatusErr` (2) | ok | Comparable targets; the rest is `errors.Is`'s walk. |
| `proto.Clone`, `CloneEntry`, `CloneConfState`, `CloneSnapshot` (4) | ok | protobuf-go v1.36.12 (the comments cite v1.36.11, same paths): a typed-nil source gives a typed nil; the merge allocates destinations for non-nil message fields (`CloneSnapshot`'s strengthened `ownSnapW` clause holds), copies bytes and repeated scalars, only reads the source. |
| `proto.EqualConfState` | ok | Repeated fields compared in order, nil equal to empty, which `ConfStateM` does not distinguish. |
| `proto.MarshalIRR`, `MarshalConfChange`, `MarshalConfChangeV2`, `Size`, `SizeEntry`, `Unmarshal`, `UnmarshalConfChange`, `UnmarshalConfChangeV2` (8) | ok | Errors where Go has them (UTF-8); proto2 conf changes without required fields; the decoder bounds-checks and does not apply closed-enum semantics. |
| `semver.MustParse` | ok | `semverValid` is "`NewVersion` accepts" (with etcd's default `CoerceNewVersion`). |
| `semver.Version.LessThan`, `Version.String` (2) | benign | Values. |
| `heap.Fix`, `heap.Push`, `sort.Stable`, `rand.Int63n`, `reflect.ValueOf`, `strings.SplitN` (6) | ok | Indices in range, `n > 0`, a unique stable order, `IsNil` on a pointer kind. |
| `math.Ceil`, `utf8.ValidString`, `go_humanize.Bytes`, `attribute.Bool`/`Int`/`Int64`/`String`, `trace.WithAttributes`, `types.ID.String`, `ID.String_ptr`, `URLs.StringSlice`, `version.Cluster`, `version.LessThan`, `etcdserverpb.AlarmType.String`, `raftpb.ConfChangeType.String` (16) | benign | Pure values or formatting. |
| `trace.SpanFromContext` | ok | The context's span or a noop span. |
| `verify.Assert`, `verify.Verify` (2) | ok | `Assert(true, …)` returns; `Verify` needs `f` to return true, excluding the panic whatever `ETCD_VERIFY` is. |
| `RangeRequest.String`, `NewLoggableTxnRequest`, `DescribeConfChange` (3) | ok | Read-only formatting (`raft/util.go:247` for the last). |

### gRPC, the client and prometheus (96; grpc v1.84.0, go-grpc-middleware providers/prometheus v1.1.0, client_golang v1.24.1, otelgrpc v0.71.0, `client/v3`; Lean: `Proof/google_golang_org/grpc/{InvGrpc,InvGrpcStream,InvDial}.lean`, `Proof/go_etcd_io/etcd/client/v3/InvClientNew.lean`, `Spec/google_golang_org/grpc/`, ...)

The predicate family is consistent: in the trivial model (`net.Listen` diverging, every server and
registration predicate `False`) every law and triple holds. The intended model: a ghost token per
server, resolver, listener and address for the exclusive predicates (`netListenerAt` only from
`net.Listen` consuming `netAddrFree`, handed out once by `goose_adequacy_start`); a persistent
ghost registry `addr ↦ name ↦ (handler, server, interceptors, S)` for `grpcServes`,
`grpcServesStream`, `grpcConn`, `grpcHealthSrv`, `promSrvMetrics`, with an invariant holding the
pool of `n` slots, `Invoke`/`NewStream` "take a slot, run the registered handler"; the pure
properties (`grpcSrvOpt`, `grpcDialOptIs`, `etcdStreamInterceptor`, ...) equalities with the value
the constructor's spec returns. Its idealisations are the two suspects and `NewStream`'s retry case.

| axiom | verdict | reason |
|---|---|---|
| `grpc.ClientConn.NewStream` | **false** (latent) | Stated for any stream description and retry option. For a server-streaming method with `max > 0` etcd's interceptor returns a `serverStreamingRetryingStream` (`client/v3/retry_interceptor.go:129-146`) that, when the first `RecvMsg` fails, opens a new stream and replays the buffered sends (231-255): the handler runs twice, which the client's one `γ` cannot describe. The one caller, `Watch`, is bidirectional with `max = 0` (`client.go:269`). Fix: require `desc.ClientStreams` or no retry with `max > 0`. |
| `prometheus.CounterVec.WithLabelValues`, `GaugeVec.WithLabelValues`, `HistogramVec.WithLabelValues`, `GaugeVec.With` (4) | **false** (latent) | Return for any labels; Go panics on a wrong label count or a value that is not UTF-8 (`counter.go:283`, `gauge.go:249`, `labels.go:166`). Every call site passes the right number of constants, ids or versions (`v3rpc/interceptor.go:63,234` checks the client version with `utf8.ValidString`). Fix: arity and UTF-8 premises. |
| `grpc.serve` | suspect | Runs at most `n` handlers at once (each run takes one of `n` copies of `S`, `InvGrpc.lean:461`); grpc-go starts a goroutine per stream with only a per-connection `MaxConcurrentStreams`. Sound while the slots stand for a bound Go cannot reach (about 2^30 concurrent runs, `notes/decisions.md`). |
| `grpc.serveStream` | suspect | A stream run keeps its copy of `S` for good (`InvGrpcStream.lean:936`), so the model starts at most `n` Watch streams **in a run**, while Go starts every one: a long run exceeds any fixed `n`. Fix: give the slot back when the stream ends. Not on putget's path (no Watch). |
| `grpc.ClientConn.Invoke` | ok | `call.go`; one attempt runs the handler at most once (no retry policy in the service config; transparent retry only when the server never saw the call). |
| `grpc.NewClient`, `grpc.NewServer`, `grpc.Server.RegisterService`, `grpc.start` (4) | ok | No connection at `NewClient`; chains concatenated in option order; one method map, covered by the distinct-names premise (`server.go:789-817`); `Serve` twice excluded by `grpcSrvNew`. |
| server options `ChainUnaryInterceptor`, `ChainStreamInterceptor`, `CustomCodec`, `MaxConcurrentStreams`, `MaxRecvMsgSize`, `MaxSendMsgSize`, `StatsHandler`; dial and call options `WithResolvers`, `WithStreamInterceptor`, `WithUnaryInterceptor`, `WithTransportCredentials`, `Peer`, `StaticMethod` (13) | ok | Each matches its constructor. |
| `GenericServerStream.Recv`/`Send`/`Context`, `GenericClientStream.Recv`/`Send`/`CloseSend`/`Context` (7) | ok | Their bodies (`stream_interfaces.go:176-237`). |
| `grpc_health_v1.RegisterHealthServer`, `status.Code`/`Error`/`Errorf`/`FromError`, `metadata.FromIncomingContext`, `metadata.MD.Get`, `otelgrpc.NewServerHandler`, `prometheus.Register` (9) | ok | `FromError` a function of the error; incoming metadata always has a value per key in the closed program; `Register` returns an error (only `MustRegister` panics). |
| `grpc_prometheus.NewServerMetrics`, `WithServerHandlingTimeHistogram`, `ServerMetrics.InitializeMetrics`, `UnaryServerInterceptor`, `StreamServerInterceptor` (5) | ok | The interceptors call the handler once and pass the stream through (`v2/interceptors/server.go:16-39`). |
| `grpcServerAt`, `grpcStreamServerAt`, `grpcSrvNew`, `grpcServeTok`, `grpcResolverAt`, `etcdResolverOwn`, `netListenerAt` (7) | ok | Model above (exclusive tokens). |
| `grpcServes`, `grpcServesStream`, `grpcConn`, `grpcHealthSrv`, `promSrvMetrics` and their `_persistent` laws (10) | ok | Model above (the persistent registry). |
| `grpcSrvOpt`, `grpcProtoCodec`, `grpcStatsHandlerOk`, `grpcDialOptIs`, `etcdStreamInterceptor`, `grpcPeerOpt`, `grpcWrotePeer`, `promSrvMetricsOpt` (8) | ok | Model above (pure equalities). |
| `v3rpc.codec_proto`, `etcdResolver_grpc`, `resolver.New`, `EtcdManualResolver.SetEndpoints`, `EtcdManualResolver.Close`, `endpoint.RequiresCredentials` (6) | ok | `v3rpc/codec.go`; `internal/resolver/resolver.go` (`Interpret(ep) = ep` for a plain endpoint, no-op callbacks); `endpoint.go:90-125`. |
| `Client.dialWithBalancer.unfold`, `Client.dialWithBalancer.builderType` (2) | **false, inconsistent in Lean; fixed** | True of Go (`client.go:311-315`; the method is names-only, so no other unfold conflicts), but stated for **every** `GoSemanticsFunctions`: at `methods := fun _ _ _ => func.nil` the unfolding of two receivers gives `λ arg1, impl v₁ arg1 = λ arg1, impl v₂ arg1`, and at `underlying := id` the named `resolver.Builder` is its interface type: `False` (checked in Lean, B1). **Fixed (B1, 2026-10-18):** the hypothesis class `DialWithBalancerBody`, taken by `Client.dialWithBalancer.wp_proof` and the results linking it (`wp_dialWithBalancer`, `wp_newClient`, `clientv3.wp_New`). |
| `Client.Endpoints`, `getToken`, `roundRobinQuorumBackoff`, `streamClientInterceptor`, `waitRetryBackoff`, `withVersion` (6) | ok | `client.go:167,285,491`, `retry_interceptor.go:112,312,360`, `ctx.go:41`. |
| `ClientConn.Target`, `insecure.NewCredentials`, `peer.Peer.String`, `HealthCheckResponse_ServingStatus.String`, `health.NewServer`, `health.Server.SetServingStatus`, `NewAuth`, `NewCluster`, `NewLease`, `NewMaintenance`, `streamKeyFromCtx` (11) | benign | Values, formatting, structs built from the connection. |

### Other etcd-internal axioms (51) and audit point 5's three

| axiom | verdict | reason |
|---|---|---|
| `convert_float64_to_int64` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/FloatToInt.lean`) | **false, inconsistent in Lean; fixed** | Stated for **every** `[GoLocalContext]`, whose one field is `is_go_step_pure`; Perennial has `Inhabited GoLocalContext := ⟨⟨fun _ _ _ => False⟩⟩` (`GooseLang/Lang.lean:476`). At that instance `isGoStep_pure_det` says `(fun _ => False) = Eq e`; applied to `e`, `False = (e = e)`: `False`, in any context with `[FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]`, which every proof here has. (Derived by hand in phase A; checked in Lean in B1, also closed from concrete instances.) `NewServer` uses it (`int64(math.Ceil(minTTL.Seconds()))`), so it is in putget's trust base. **Fixed (B1, 2026-10-18):** the hypothesis class `Float64ToInt64Semantics` (the function a field, as `FloatOps`'s), taken by `NewServer.wp_proof` and `wp_NewServer` (`gen-link.py`'s `SEM_PREMISES`); a closed theorem takes it as a premise on the local context (D19a). |
| `storage.NewBackendQuota` | **false** | Its post `isQuota` says `Available` always answers true (`apply/Contracts.lean`, "a construction premise"); Go's `Available` (`storage/quota.go:126-134`) is false once `be.Size() + cost ≥` the quota (2 GiB by default). It also panics on a nil backend, and with a negative quota on a nil logger (`quota.go:80`). On putget's `Put` path (the quota applier, `quotaKVServer`); putget stays far below the quota. This is what hides the NOSPACE alarm (`EtcdServer.Alarm`, `raftRequestAlarm` above) from the model. Fix: a named "the backend stays under its quota" premise. **Fixed (B3, D19h option (B), 2026-10-18):** restated under the opaque workload premise `apply.backendUnderQuota` (every `Available` of the run answers true), a premise of the constructions above it up to `NewServer.spec` and `v3rpc.Server`; true of Go given it. |
| `mvcc.store.Close` | **false** | `kvstore.go:515-518` stops the FIFO scheduler, but `isStore` is persistent and contains `schedLive` ("never stopped"), so `store.Compact` after `Close` checks out while Go's `Schedule` panics ("schedule to stopped scheduler", `pkg/schedule/schedule.go`). Only on `NewServer`'s error path (`server.go:380`). **B4a (2026-10-18): stopped, needs a decision (D19m)**: any true contract needs the stop token `NewStore` gives up; options: a fractional "store open" token, `NewServer`'s late error paths dead, or `NewStore` returning the stop token for its caller to give up on success (recommended). |
| `membership.RaftCluster.SetVersionChangedNotifier` | **false** | Writes `c.versionChanged` without the lock (`cluster.go:252-254`; the spec's comment says under it) with only the persistent `isRaftCluster`; a concurrent `SetVersion` would race. Called once in `NewServer` before `Start`. Fix: the field's points-to. Does not bear on `localKept` (2026-10-18: the lock invariant describes the members map and the local id only). **Fixed (B4a, 2026-10-18):** the contract takes `c.versionChanged`'s points-to and returns it at `n`; `bootstrap`'s contract gives the field owned (`bootOk`'s `Hvcn`), `NewServer` persists it after the call, and the cluster's apply contract (`Hisc`, whose `SetVersion` reads it) takes it read-only (D19m). Still an axiom (names-only), restated. |
| `mvcc.store.restore` | **false** (premise gap) | The precondition fixes only the `key` bucket; a `meta` bucket with a finished or scheduled compaction and an empty `key` bucket makes Go set `compactMainRev`/`currentRev` to other values and call `compactLockfree` (`kvstore.go:330-417`). It also reads through `ReadTx` without `isKeyBackendG`'s `RT`, and writes `currentRev` with half of it (documented). putget's backend is fresh. |
| `lease.lessor.Promote` | **false** (premise gap) | A negative `leaseRevokeRate` with an empty lease map indexes `leases[0]` (`lessor.go:494-503`); `NewLessor.spec` accepts any configuration (only 0 is defaulted). `NewServer` leaves it 0. |
| `addFeatureGateMetrics` | **false** (premise gap) | Any non-null `*featureGate`; a zero one panics at `f.known.Load().(map…)` (`feature_gate.go:329,335`). Fix: `isFeatureGate`. |
| `monitorFileDescriptor` (`metrics.go:215`) | **false** (premise gap) | No `lg ≠ null`; it calls `lg.Warn` when `FDUsage`/`FDLimit` fail or usage reaches 80 % (226-237). The caller passes `s.Logger()`. |
| `mvcc.hashStorage.Store`, `mvcc.kvHasher.WriteKeyValue`, `mvcc.kvHasher.Hash` (3) | **false** (premise gap) | Any receiver (a zero `hashStorage` panics at `s.lg.Info`, `hash.go:157`; a zero `kvHasher`'s nil hash at `Sum32`, `hash.go:93`) and any key (`BytesToBucketKey` panics unless it is a 17/18-byte revision key, `revision.go:98-108`). Callers (`kvstore_compaction.go:48-74`) meet them. |
| `storage.BackendQuota.Cost`, `txn.WarnOfExpensiveRequest`, `txn.WarnOfFailedRequest` (3) | **false** (premise gap) | A nil request (`quota.go:149`) or a nil logger/stringer (`txn/util.go:46-49, 93-98`) panics; callers pass real ones. |
| `auth.authStore.AuthInfoFromTLS` | **false** (known) | `peer.AuthInfo.(credentials.TLSInfo)` (`auth/store.go:1019`) panics on a non-TLS `AuthInfo`; the spec takes any context. Filed: `issues/etcd-auth-tls-info-assert.md`. putget has no server credentials (`AuthInfo` nil). |
| `membership.localKept`, `localKept_persistent` (2) | **removed (2026-10-18)** | Model: `True`. A premise of `IsLearner`'s spec that nothing produced: the closed theorem supplied it. Now defined: the cluster's lock invariant keeps the local member (`rcLockInv`'s `rcLocalIn`), `localKept c := isRaftCluster c`, from `bootstrap`'s contract; the only removal, `applyConfChange`'s `RemoveNode`, excluded since B3 (`ccApplyOk`). Two axioms fewer. |
| `lease.NewLessor`, `lessor.Demote`, `lessor.scheduleCheckpointIfNeeded` (3) | ok | Memory under `le.mu` only; `runLoop`'s proposals go through `expiredC` (the server's `revokeExpiredLeases`) and the checkpointer, under the named premise `ckptEffectsOk`. |
| `auth.NewAuthStore`, `auth.NewTokenProvider`, `v3alarm.NewAlarmStore` (3) | ok | `auth/store.go:944-992, 1090-1157`, `alarms.go:44-114`; putget's empty `AuthToken` gives `tokenNop`. |
| `rafthttp.Transport.Start`, `AddPeer`, `AddRemote` (3) | ok | `transport.go:134-325`; the peers' goroutines under the named premise `transportEffectsOk`; not called for a single member. |
| `schedule.NewFIFOScheduler`, `Scheduler.Schedule`, `Scheduler.Stop` (3) | ok | The panic after `Stop` is excluded by the tokens (the flaw is `store.Close`'s). |
| `v3compactor.New`, `pbutil.MustUnmarshalMessage`, `schema.MustUnsafePutLease`, `schema.MustUnsafeSaveConfStateToBackend`, `mvcc.newKVHasher`, `mvcc.store.HashStorage` (6) | ok | `New` starts no goroutine; the decode premises exclude the panic; one `UnsafePut` each; a fresh value, a field read. |
| `membership.RaftCluster.String`, `auth.hasRootRole`, `config.ServerConfig.PeerDialTimeout`, `v3rpc.NewMaintenanceServer`, `v3rpc.logUnaryRequestStats`, `traceutil.Tracer.Start`, `traceutil.Trace.LogWithStepThreshold` (7) | ok | Reads and logging (no `traceutil.Init` in putget). |
| `api.IsCapabilityEnabled`, `auth.redactToken`, `newCorruptionChecker`, `v2stats.NewLeaderStats`, `NewServerStats`, `ServerStats.BecomeLeader`, `txn.ApplySecObserve`, `txn.RangeSecObserve`, `v3rpc.isClientCtxErr` (9) | benign | Metrics, fresh values, stats under a lock, pure functions. |
| `EtcdGrove.goose_adequacy_start` (point 5) | ok | Perennial's `goose_adequacy` (`GooseLang/Adequacy.lean:274`) plus the start rights handed out once; consistent with `nameFree`/`netAddrFree` as `True`, though the gRPC family's intended model needs `netAddrFree` exclusive per address. It rests on the user checking `namesUnclaimed`/`addrsUnclaimed`. |
| `EtcdGrove.initLb_of_spec` (point 5) | ok | Only for the Goose-generated `ExternalInit`s, whose package-state map only grows. |
| `features.NewDefaultServerFeatureGate` (point 5) | ok | `New` stores both maps and `Add` registers the 10 features (`etcd_features.go:99-118`), exactly `serverFeatures`. |
