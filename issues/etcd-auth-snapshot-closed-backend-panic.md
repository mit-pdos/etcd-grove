---
upstream: none
checked: 2026-10-19
links:
  - etcd-io/etcd#17223 issue closed: the same nil read tx (`UnsafeRange` on a closed backend), reached at shutdown; closed by #17757 and gRPC's GracefulStop draining handlers, which do not cover a snapshot install
  - etcd-io/etcd#21873 pr closed: the same class (a holder of `s.be` using it across applySnapshot's swap and close), for `monitorKVHash`; not merged
  - etcd-io/etcd#13883 issue closed: a different `authStore.Recover` bug (its caches were not refreshed), fixed by #13920
  - etcd-io/etcd#22189 issue open: the same nil read tx of a closed backend, from `Maintenance/Status` during shutdown; not this path
  - etcd-io/etcd#22190 pr open: the fix of #22189 (`StorageVersion` only); does not fix this
  - etcd-io/etcd#14256 issue closed: the same `Tx.Bucket` stack from watch at shutdown (3.4)
candidate: issues/upstream/etcd-auth-snapshot-closed-backend-panic/
---

# A member with auth enabled panics on a permission check while it installs a leader's snapshot

- **Status**: a bug (a reachable nil-pointer panic in a gRPC handler, which crashes the member).
  It needs auth enabled; the rest is normal operation: a lagging member catches up by a
  snapshot while clients send it requests. Reproduced end to end by an integration test, at the
  pin (7 of 10 runs) and on upstream `main` (3 of 3). The fix (below) is to close the old backend
  last. With it the test passes 6 of 6 runs at the pin and 3 of 3 on `main`.
- **Where**: at the etcd pin of `etc/goose.py` (`8a24be2a3`; upstream `main` `6782f5229` has
  the same code, at `server.go:1083-1111`):
  - `server/etcdserver/server.go:1011-1159` (`applySnapshot`): `s.be = newbe` (`:1093`), then
    `go oldbe.Close()` (`:1100-1110`), then `s.restoreAlarms()` (`:1112`, which ends with a
    `ForceCommit` of the new backend: an fsync), and only then
    `s.authStore.Recover(schema.NewAuthBackend(lg, newbe))` (`:1121`). Until `Recover` sets it,
    the auth store's `as.be` is the old backend (`schema/auth.go`'s `authBackend.ReadTx` calls
    `abe.be.ReadTx()` on it).
  - `server/storage/backend/backend.go:463-488`: `Close` stops the batch loop, which runs
    `batchTx.CommitAndStop()`. That calls `unsafeCommit(stop=true)` (`batch_tx.go:381-406`), which
    calls `readTx.reset()` (`read_tx.go:133-138`: `rt.tx = nil`, an empty bucket cache) and
    opens no new read transaction.
  - `server/storage/backend/read_tx.go:78-122` (`baseReadTx.UnsafeRange`): after a reset the
    buffer and the bucket cache are empty, so the bucket is looked up with
    `baseReadTx.tx.Bucket(...)` (`:103`) on the nil `*bolt.Tx`. bbolt's `Tx.Bucket` is
    `tx.root.Bucket(name)` (`bbolt@v1.5.0/tx.go:112`): a nil-pointer dereference. There is no
    closed check.
  - `server/auth/store.go`: the checks that read `as.be` with no lock: `CheckPassword`
    (`:361-394`), `isOpPermitted` (`:859-899`, under `IsRangePermitted`/`IsPutPermitted`/
    `IsDeleteRangePermitted`) and `IsAdminPermitted` (`:913-935`). Each does
    `as.be.ReadTx()`, `RLock`, `UnsafeGetUser`. The store's locks do not cover this read:
    `enabledMu` guards `enabled`, `rangePermCacheMu` the permission cache, read after the user
    lookup. The token provider (`AuthInfoFromCtx`) does not touch the backend. `s.bemu` guards
    `s.be` only, and `applySnapshot` releases it before the close begins.
  - They run on gRPC goroutines, before (or without) going through raft:
    `EtcdServer.doSerialize` (`v3_server.go:1035-1057`, from `Range`/`RangeStream`/read-only
    `Txn`), the watch create's `IsRangePermitted` (`v3rpc/watch.go:246`), `checkLeaseRenew`
    (`v3_server.go:575-605`, from `LeaseKeepAlive`), `Authenticate`'s `CheckPassword`
    (`v3_server.go:853`), and `AuthAdmin.isPermitted` (`v3rpc/auth.go:182-189`, from the
    maintenance RPCs). etcd installs no panic recovery: `v3rpc.Server` (`v3rpc/grpc.go:44-95`)
    chains only logging, metrics and etcd's own interceptors, and `embed` passes no extra
    interceptor (`embed/serve.go:184,244`). A linearizable `Range` is not exposed: its read
    index is at least the snapshot's index, so it waits for the apply loop until after
    `applySnapshot` has returned. A serializable one is exposed.
- **What happens**: during the window from the old backend's `CommitAndStop` (in the close
  goroutine) to the end of `authStore.Recover`, every serializable read, watch create, lease
  keep-alive, `Authenticate` or admin RPC that reaches the member hits a nil `*bolt.Tx` and
  panics. The process exits. On a member that is behind, the window is the time `restoreAlarms`
  takes, including its fsync. A request that had already taken the old backend's read lock
  completes safely, because `CommitAndStop` takes the write side of that lock first.

  Reproduction: `issues/etcd-auth-snapshot-closed-backend-panic/repro_test.go`. Copy it into
  `tests/integration/` and run `go test ./integration -run
  'TestAuthStoreCheckOnClosedBackend|TestV3AuthReadDuringSnapshotInstall' -count=1 -v` from
  `tests/`.
  - `TestAuthStoreCheckOnClosedBackend` (unit level, deterministic) builds the state
    `applySnapshot` leaves in the window. It creates an auth store on a temporary backend, adds
    `root`, enables auth and closes the backend. Then each of `IsRangePermitted`,
    `IsPutPermitted`, `IsAdminPermitted` and `CheckPassword` panics with `runtime error: invalid
    memory address or nil pointer dereference`, at `bbolt.(*Tx).Bucket` ← `read_tx.go:103` ←
    `schema.unsafeGetUser` ← the check. (Each check gets a fresh store: the panic leaves the read
    tx's `txMu` locked, so a second check on the same backend blocks.) This shows the closed
    backend panics. The test below shows that the window is reached.
  - `TestV3AuthReadDuringSnapshotInstall` (end to end) uses 3 members, `SnapshotCount: 10` and
    `SnapshotCatchUpEntries: 5`, with auth enabled (`root`). It cuts a follower off from its
    peers, makes 40 puts through the leader, starts 32 goroutines sending serializable `Get`s
    as `root` to the follower, then heals the partition. The follower then installs the leader's
    snapshot (the test checks that `Server.Backend()` changed). Results at the pin: 7 of 10 runs
    panic, about 0.5 s in. The goroutine's stack is
    `bbolt.(*Tx).Bucket` ← `read_tx.go:103` ← `auth_users.go:57` ← `authStore.isOpPermitted`
    (`store.go:883`) ← `IsRangePermitted` ← `EtcdServer.Range` (`v3_server.go:146`, via
    `doSerialize`) ← `kvServer.Range`. The member's log stops at `restoring auth store`, after
    `closing old backend file` and `restored alarm store`. On `main`, 3 of 3 runs panic with the
    same stack. The runs that pass also installed the snapshot once, with about 2900 reads
    during the run.
- **Expected**: installing a snapshot is internal to a member. A permission check reads the auth
  store's current backend, or one still open, and returns a result or an error. Nothing documents
  that a member can crash on a client request while it catches up.
- **Same class, narrower windows** (found by reading the code, not reproduced): other holders of
  the old backend that can use it after its close has begun.
  - `store.hash()` (`mvcc/kvstore.go:156-163`, behind the maintenance `Hash` RPC) reads `s.b`
    twice without `s.mu`. `store.Restore` replaces `s.b` under `s.mu` before the swap, so a
    `Hash` that loaded the old `s.b` just before can run its `ForceCommit` or `Hash` on the
    closing backend. If the commit loop has stopped, `ForceCommit`'s `batchTx.commit(false)` begins
    a new bolt transaction: a `Fatal` (`failed to begin tx`) if the db is closed, or a write
    transaction that is never committed, which `db.Close` then waits on. `Hash` on a closed db
    returns an error.
  - The maintenance `Snapshot` RPC (`v3rpc/maintenance.go:141,146`) takes `ms.bg.Backend()` twice
    and uses each result after `bemu` is released. `ReadStorageVersion(…ReadTx())` on a reset read
    tx is the same nil-tx panic. `Snapshot()` on a stopped backend has the same `begin` problem.
  - The gRPC quota servers keep a backend captured at startup:
    [etcd-quota-stale-backend-after-snapshot](etcd-quota-stale-backend-after-snapshot.md)
    (wrong results there, not a crash).
- **How the proof handles it**: not yet. Today no member installs a snapshot (`bootOk`'s
  `"%Hnosnap"`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean:56,202`),
  and `applySnapshot`'s spec covers only the empty snapshot. The auth store's invariant holds
  `as.be` as a persistent read-only field (`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean:10-11`,
  `:167`; `Recover` is left out). Its backend contract `authBackendOk`/`authReadTxOk`
  (`InvAuth.lean:121-138`, assumed, not proved of the real backend) says `ReadTx`/`UnsafeGetUser`
  always return. A closed backend does not meet that contract. Track T-S (the snapshot path,
  `notes/decisions.md` D22) has to restate both: `be` is replaced by `Recover`, and the old
  backend's reads stay valid only until its close.
- **Possible fixes**:
  1. Close the old backend last: move the `go oldbe.Close()` block after `restoreAlarms`,
     `authStore.Recover` and `cluster.SetBackend`
     (`issues/etcd-auth-snapshot-closed-backend-panic/fix.patch`, which also applies to `main`).
     With it the end-to-end test passes 6 of 6 runs at the pin and 3 of 3 on `main`. A small
     window is left: a check that read `as.be` (old) just before `Recover` and calls
     `ReadTx`/`RLock` after the close has started. `as.be` is also written by `Recover` and read
     by gRPC goroutines with no synchronization, which is a data race.
  2. A complete fix also guards `as.be`: Recover would take a lock (or set an
     `atomic.Pointer`), and the checks would hold it from loading `as.be` until `RUnlock`. Or the
     backend would refuse reads after close (`baseReadTx` would check `tx == nil` and return
     empty, or error, instead of dereferencing). The same applies to `store.hash` (take `s.mu`
     for reading) and to the maintenance `Snapshot` (hold `bemu` for reading across its two uses,
     as `StorageVersion()` does).
- **Found**: 2026-10-19, from a review of `applySnapshot`'s backend swap while scoping track
  T-S (the snapshot path). It looked at the holders of the old backend after the swap.
