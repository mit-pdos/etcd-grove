# Axiom audit (Lean port)

**Started:** 2026-10-18, branch `raft-retarget`. **Why:** the closed adequacy theorem (item 9)
is only as sound as the axioms it rests on, and the trust base (`etc/tcb-baseline.txt`, 327
axioms, 12 `sorry`s) has grown one names-only spec at a time. An axiom here is a claim about Go
code that nobody checked mechanically; a false one can make the closed theorem prove something
false of Go. This file records each axiom's verdict, the reason, and the fix.

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
- **Phase C:** models for the **suspect** predicate families (bbolt/backend, gRPC), or a
  narrower set of laws.

## Table

Verdicts are for the instances the proofs use. **A caveat common to the names-only contracts** whose
precondition is only `isPkgInit` (`∀ s, {{ isPkgInit }} s.m(…) {{ True }}`): read literally they
are false for an `s` that is not a live server (the Go body dereferences `s`); no proof
instantiates them so, and the rows below do not repeat it.

### `etcdserver` (`EtcdServer.*`, the names-only methods; Go: `server/etcdserver/server.go` unless
named; specs: `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__<m>.lean`)

| axiom | verdict | reason |
|---|---|---|
| `EtcdServer.compactRaftLog` | **false** | Point 1 confirmed. `compactRaftLog` (2132) calls `s.r.raftStorage.Compact(compacti)`, whose spec (`Spec/go_etcd_io/raft/v3/MemoryStorage__Compact.lean`) needs raft's `ownMemoryStorage` with nothing pending; the contract owns only `srvLgReader s`. Reached much earlier than point 1 said: `snapshotIfNeededAndCompactRaftLog` (1210) runs it whenever `shouldSnapshotToMemory` holds, i.e. every `memorySnapshotCount = 100` applied entries (116), not only at `SnapshotCount = 10000`. Go itself is fine (the storage's mutex); the model is wrong. |
| `EtcdServer.snapshot` | **false** | Point 2 confirmed. `snapshot` (2078) calls `s.r.raftStorage.CreateSnapshot(ep.appliedi, ep.confState, nil)`, whose spec needs `ownMemoryStorage` (nothing pending) and since D17d `memSnapTok`; with `toDisk` it also writes the WAL and the snapshotter (`s.r.storage.SaveSnap`, `Release`), which the raft loop writes concurrently. The contract owns none of them. Reached with `compactRaftLog` (every 100 applied entries). `KV().Commit()` is covered by `applyBackend`/`srvApplyKV`. |
| `EtcdServer.applyConfChange` | **false** (as stated) | For every change `m`: (a) it calls `s.r.ApplyConfChange(cc)` (2008, 2022), i.e. raft's `node.ApplyConfChange`, whose spec (`Spec/go_etcd_io/raft/v3/node__ApplyConfChange.lean`) needs `CCShrink` in the static mode or `DynCCPreOp`, and raft's `isNode`; the contract asks for neither, so it changes raft's configuration outside raft's proof; (b) it panics (`lg.Panic`, here and in `membership.ValidateConfigurationChange`, `cluster.go:321,377,386`) on a context that is not the JSON of a member or an unknown type, which the contract does not exclude; (c) `RemoveNode` of the local member deletes it from `c.members` (`RemoveMember`), contradicting the persistent `membership.localKept`. Reached in putget: the bootstrap's `AddNode(self)` entry (validation passes, `membersFromBackend` is empty on a new backend; `AddMember` rewrites the member, no `AddPeer`); that instance is plausibly true (a change raft already applied at `Bootstrap`), so the fix is to restrict `m` (to `CCShrink` and well-formed contexts, as `node.ApplyConfChange` does). |
| `EtcdServer.createMergedSnapshotMessage` | **false** | `snapshot_merge.go:32` commits the backend (`s.KV().Commit()`), takes a backend snapshot (`s.be.Snapshot()`, a bbolt read transaction streamed by a goroutine), reads `*confState` (`proto.Clone`) and writes `m.Snapshot`; the contract owns no backend, no `m` (the `msgSnapC` bag's predicate gives none) and no `cs`. Only on a leader with a follower that needs a snapshot: not reached in single-member putget. |
| `EtcdServer.sendMergedSnap` | suspect | Writes `s.inflightSnapshots` (an atomic that `compactRaftLog` reads), hands `merged` to `s.r.transport.SendSnapshot`, and `GoAttach`es a goroutine; nothing in the model owns these, so it is sound only while nothing does. Not reached in putget (no `MsgSnap`). |
| `EtcdServer.revokeExpiredLeases` | **false** (as stated) | For a non-empty `leases` (854) its goroutine proposes `LeaseRevoke` through `s.LeaseRevoke`→`raftRequest` with no `reqPropOk` (a revoke deletes the lease's keys: the KV workload invariant can break) and calls `ensureLeadership` (`s.read.LinearizableReadNotify`); the contract takes nothing. Not reached in putget's Go execution (no lease is granted, so `ExpiredLeasesC` never fires), but `run`'s proof uses it for every `leases`. |
| `EtcdServer.raftRequestAlarm` (`AlarmContract.lean`) | **false** (as stated) | A second contract of the *verified* `raftRequest` for **every** `InternalRaftRequest` `v` (`p ↦ v`), with no `reqPropOk`, id credit or reader slots: it lets a proof propose a `Put`/`Txn` outside the KV workload invariant. The one use (`applyEntryNormal`'s NOSPACE goroutine) proposes `{Alarm: {ACTIVATE, NOSPACE}}`, which is a non-write `plainReq`; restrict `v` to that request and the instance used is plausibly true. |
| `EtcdServer.monitorStorageVersion` | **false** | Its monitor (`version/monitor.go:108`) calls `UpdateStorageVersion` (`adapters.go`): `s.be.BatchTx()` with `LockOutsideApply`, then `schema.UnsafeMigrate`, which writes the meta bucket's `storageVersion` (`migration.go:101`); the backend and its batch lock are the apply thread's (`applyBackend`, `batchLockInv`). **Reached in putget**: once `monitorClusterVersions` sets the cluster version (3.7; `firstCommitInTerm` fires at the leader's first commit) the storage version is detected as 3.5 (no `storageVersion`, term > 0: `UnsafeDetectSchemaVersion`) and migrated, on `clusterVersionChanged` or after 4 s. |
| `EtcdServer.monitorKVHash` | **false** (as stated) | With `CorruptCheckTime ≠ 0` it reads the whole backend (`VerifyBackendConsistency`, `PeriodicCheck`'s `HashByRev`) and on a mismatch proposes `Alarm{CORRUPT}` through `raftRequest` (`corrupt.go`, `TriggerCorruptAlarm`), none of it owned or permitted. Returns at once in putget (`CorruptCheckTime = 0`, 2246). |
| `EtcdServer.monitorCompactHash` | **false** (as stated) | With the `CompactHashCheck` feature on, `CompactHashCheck` reads the store's hashes and may propose `Alarm{CORRUPT}`; nothing owned or permitted. Returns at once in putget (the feature is off by default, 2276). |
| `EtcdServer.monitorDowngrade` | **false** (as stated) | With `DowngradeCheckTime ≠ 0` and a downgrade enabled, `CancelDowngradeIfNeeded` proposes `DowngradeInfoSet` (`adapters.go`, `DowngradeCancel`) without a permit (not in `monitorReq`). Returns at once in putget (`DowngradeCheckTime = 0`, 2336). |
| `EtcdServer.publishV3` | suspect (minor) | D19c's restriction holds: it proposes only `ClusterMemberAttrSet` (1793). But `raftRequest`'s spec also needs a reader slot of `leadTimeMu` (`srvLeadTimeReader`, an `ownRWMutex`), the auth reader `E.RD` and `mvcc.idxCert`, which the persistent `srvMonitorPermit` does not give; true of Go (a read lock) only if the model can mint such slots freely. It also closes `s.readych` (no owner in the model). |
| `EtcdServer.monitorClusterVersions` | suspect (minor) | As `publishV3`: it proposes only `ClusterVersionSet` of a parsed `semver` (`updateClusterVersionV3`, through `GoAttach`), but the reader slots are not in its precondition. It also reads `s.cluster` and asks the peers' versions over HTTP (`getMembersVersions`). |
| `EtcdServer.adjustTicks` | ok | Reads `s.cluster.Members()` under the cluster's mutex and the transport's active peers, and calls `s.r.advanceTicks` (single member: `ElectionTicks − 1` ticks), whose proof takes only the persistent `isRaftNode` (each tick's credit from a time receipt). Waits at most `ConnReadTimeout`. |
| `EtcdServer.purgeFile` | ok | Removes old `*.snap.db` files in the snap directory (not the backend's `db`) and, with `MaxWALFiles > 0`, old WAL files; `lg.Fatal` on an error (diverges). No state the model owns. |
| `monitorFileDescriptor` (`metrics.go:215`) | benign | Reads the fd usage and limit, sets two gauges, logs. |
| `EtcdServer.stopWithDelay` | ok | Waits, then a non-blocking send on `s.errorc`, a bag with a trivial predicate (`InvRun.lean`). |
| `EtcdServer.Cleanup` | **false** (as stated) | Stops the lessor and compactor and closes the KV, the auth store and the backend (`be.Close` commits the batch transaction and closes bbolt), which the model's invariants keep describing as live; request goroutines (not in `s.wg`) can still use them. Only on `run`'s shutdown, which putget never reaches. |
| `EtcdServer.Alarm` (`v3_server.go:805`) | ok | `raftRequest` with `{Alarm: r}` and a type assertion that holds (the applier answers `*pb.AlarmResponse`, possibly a typed nil); the precondition is `raftRequest`'s but `reqPropOk`, which holds for an alarm (a non-write `plainReq`, its left disjunct). |
| `EtcdServer.IsLearner` | ok | `IsLocalMemberLearner` (`cluster.go:786`) under the cluster mutex; its panic is excluded by `membership.localKept` (but see `applyConfChange` (c)). |
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
