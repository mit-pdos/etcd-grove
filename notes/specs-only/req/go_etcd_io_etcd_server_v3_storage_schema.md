# Requirements on `go_etcd_io_etcd_server_v3_storage_schema`

## from 2e

Provisional, to be replaced by 4b's names:
1. `Membership.beMembers mb st` (the `MembershipBackend`'s member and removed buckets hold `st`),
   which `RaftCluster.SetBackend` turns into the cluster's `beView c st`; `MustSaveMemberToBackend`,
   `MustDeleteMemberFromBackend`, `MustReadMembersFromBackend` move/read it as the writers do.
2. `V3alarm.beAlarms be al` / `V3alarm.alarmBe ab al` (the alarm bucket; `NewAlarmBackend(lg, be)`
   turns the first into the second); `MustPutAlarm`, `MustDeleteAlarm`, `GetAllAlarms`.
Used by `RaftCluster.*.spec`, `NewAlarmStore.spec`, `AlarmStore.Recover.spec`, `restoreAlarms.spec`.

## from 3c

1. **`Lease.beLeases be B`** (provisional in `lease/Api.lean`; exclusive, timeless): the lease bucket
   of `be`, as its batch transaction holds it (the last commit with the pending writes), decodes to
   `B : Int → Option Int` (id to stored `TTL`; each record a `leasepb.Lease` that unmarshals, its
   `RemainingTTL` not modelled). Its holder is the bucket's only writer. The schema's functions, on a
   batch transaction of `be` whose lock is held (`beHook`'s `LockInsideApply`, `beTxHeld`, or
   `LockOutsideApply`):
   * `UnsafeCreateLeaseBucket(tx)`: `B` unchanged (the bucket exists or is created empty);
   * `MustUnsafeGetAllLeases(tx)`: no panic (the records decode), a fresh slice of fresh
     `*leasepb.Lease` whose `(ID, TTL)` are exactly `B`'s entries, each once;
   * `MustUnsafePutLease(tx, &leasepb.Lease{ID, TTL, RemainingTTL})`: `B` at `ID := TTL`;
   * `UnsafeDeleteLease(tx, &leasepb.Lease{ID})`: `B` without `ID`.
   Introduced by the backend's opener (2e's `OpenBackend`, `OpenSnapshotBackend`: the image's
   bucket, empty for a new member). Used by: `NewLessor.spec`, `lessor.Recover.spec`,
   `lessor.initAndRecover.spec`, `Lease.persistTo.spec`, `lessor.Revoke.spec`.
   ```go
   lpbs := schema.MustUnsafeGetAllLeases(tx)                                    // lessor.go:813
   schema.UnsafeDeleteLease(le.b.BatchTx(), &leasepb.Lease{ID: int64(l.ID)})  // :359
   ```
2. **`semver`** (the boundary 4b owns): `version.LessThan(first, second)` on two values returns
   (no panic); `version.V3_6` initialized. Used by: `greaterOrEqual.spec`,
   `lessor.shouldPersistCheckpoints.spec`.

## from 3e

mvcc's storage contract (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiStorage.lean`) names the
bucket values and key names by pure constants; the schema's initialization must give them:

1. **The buckets**: `globalAddr schema.Key ↦□ Mvcc.bucketVal .keyB` and `globalAddr schema.Meta ↦□
   Mvcc.bucketVal .metaB` (read-only after init), the two distinct; and **the compaction keys' names**:
   `globalAddr schema.ScheduledCompactKeyName ↦□ sl ∗ sl ↦*□ Mvcc.metaKey .sched` (`"scheduledCompactRev"`),
   likewise `FinishedCompactKeyName` (`"finishedCompactRev"`). A law of 4b's init (as the cache's `init`).
2. **`UnsafeCreateMetaBucket(tx)`** (`schema/cindex.go:25`): on the storage's batch transaction with the
   lock held (`Mvcc.kbLocked B D`): `tx.UnsafeCreateBucket(Meta)`, so `kbLocked B (D.create .metaB) ∗
   kbMade B .metaB` (the contract's row). Used by `NewStore.spec`.
   ```go
   tx.UnsafeCreateBucket(schema.Key); schema.UnsafeCreateMetaBucket(tx)   // kvstore.go:121-122
   ```
3. The `Key` bucket is the backend's safe-range bucket (`safeRangeBucket: true`) and `Meta` is not:
   4a's `UnsafeDelete` row of the contract takes the safe-range lock for `Key` only.

## from 3d

The auth store (`Spec/go_etcd_io/etcd/server/v3/auth/`) is stated over one provisional slot of this
package: **`Auth.authBackendAt be a`** (exclusive): `be` is an `AuthBackend` (`schema.NewAuthBackend(lg,
be)`'s `*authBackend`) whose three auth buckets (`auth`, `authUsers`, `authRoles`) hold the auth
state `a` (W0's `AuthState`): the enabled flag and revision keys, each user's `authpb.User` (its
password a bcrypt hash of the model's, `Bcrypt.hashOf`; `Options.NoPassword` for none; its roles
sorted), each role's `authpb.Role` (its permissions, in some order). With the contracts the store
calls:

1. `BatchTx()`, `Lock()`/`Unlock()` (the writer's: `Unlock` publishes the writes to the read
   transactions), `UnsafeGetUser`, `UnsafeGetRole`, `UnsafeGetAllUsers`, `UnsafeReadAuthEnabled`,
   `UnsafeReadAuthRevision`, `UnsafePutUser`, `UnsafeDeleteUser`, `UnsafePutRole`,
   `UnsafeDeleteRole`, `UnsafeSaveAuthEnabled`, `UnsafeSaveAuthRevision` (the state moves by the
   written records); a record whose key or value exceeds bbolt's limits is fatal
   (`Auth.recordsFit` is the store's premise).
2. `ReadTx()`, `RLock()`/`RUnlock()` (a reader slot, lent by the reader's `threadTok`), the same
   reads (`UnsafeGetAllRoles` is not used on a read transaction:
   `nonissues/etcd-auth-readtx-getallroles-panics.md`): the state last published.
3. `GetUser`, `GetAllUsers`, `GetRole`, `GetAllRoles` (the batch transaction's view, called by the
   writer only), `CreateAuthBuckets`, `ForceCommit`.
4. A replaced backend (the store's `Recover`) is given back as `authBackendAt be0 a0`; closing it
   waits for the read transactions still open on it (4a).
Used by: `NewAuthStore.spec`, `authStore.Recover.spec`, and every admin and check spec's proof
(`Internal.lean`'s `txAt`, `rdTx`).
```go
tx := as.be.BatchTx(); tx.Lock(); user := tx.UnsafeGetUser(r.Name)   // auth/store.go:433
tx := as.be.ReadTx(); tx.RLock()                                     // lockedReadTx
```
