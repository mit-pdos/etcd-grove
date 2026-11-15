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

mvcc's storage contract (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ApiStorage.lean`) names the
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

The auth store (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/auth/`) is stated over one provisional slot of this
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

## from 4a

4a's vocabulary (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/Api.lean`, namespace `Backend`) for
the bundles of 4a's req "from 4b": parts are footprints of cells (`Cell.bkt b`, `.key b k`, `.buf
b`); `beCur γ F C` the batch view, `beVis γ F V` the published view (or `beNoVis γ F`: nobody reads
it through read transactions), `beSess γ q F S` the lock held; `beHist` the committed images
(durable); `bucketOk bv bi` a `Bucket` value's identity. Your `txRd`/`txRange`/`txWr` at `R V := ∃ …,
beSess … ∗ beCur γ G C ∗ ⌜V matches C on S⌝` (batch) and `R V := beRd γ rt G V' ∗ …` (read) are what
4a would prove, with differences in your rows that etcd's backend does not meet:

1. **`txWr`'s `UnsafePut` needs the entry bound** `k.length + v.length ≤ Bbolt.bboltEntryMax` (4c's:
   a larger value bbolt accepts but cannot commit or read back, `issues/bbolt-max-value-size-unusable.md`).
   4a's `batchTxBuffered.UnsafePut.spec` takes it (and, in a safe-range bucket, `Sess.fresh`: none
   of yours).
2. **`txRd`'s `UnsafeForEach` on a read transaction is not in key order**: `baseReadTx.UnsafeForEach`
   (`read_tx.go:52-73`) visits bbolt's entries the read buffer does not shadow, then the buffer's:
   two sorted runs (`Backend.rdOrder`), each entry once; in key order only on the batch transaction
   (`btOrder`). Your users collect into sets or maps (alarms, members, users), so "each entry once,
   in some order" should serve.
3. **`bucketOk`**: please give `Schema.bucketAt b bv ⊢ Backend.bucketOk bv ⟨b.name, b.id, b.safe⟩`
   (with ids distinct across buckets: `Backend.bucketOk_id`, which the read buffer, keyed by id,
   needs).
4. **`applyHook be Pre Q`** is 4a's `batchTxBuffered.LockInsideApply.spec` with `beHook γ dq f ∗
   hookRun Pk f Pre Q` (`Backend.hookRun`); `Commit`/`ForceCommit` take `Backend.beReq γ Pk X Y`.
5. **`ReadTx()` read without `RLock` under the batch lock** (your item 3): `Backend.beSess_rd`.
6. **`Meta`'s existence** is shared: whoever first creates it (bootstrap) freezes it
   (`beCur_freeze` gives `beMade γ "meta"`); `UnsafeCreateBucket(Meta)` is then a no-op for every
   user (`batchTxBuffered.UnsafeCreateBucket.spec`'s `none` case).

## from 4a, round 1

1. **`Backend.bucketOk` is now transparent** (the bundle of `ID()`, `Name()` (read-only slice),
   `IsSafeRangeBucket()` triples, `Api.lean`): please prove `bucketAt b bv ⊢ Backend.bucketOk bv
   ⟨b.name, b.id, b.safe⟩` (a law of yours: your `bucket.*.spec` give it). Id uniqueness is no
   longer a law of `bucketOk`: `New` takes the declared set `Bs` (`bktsOk Bs`) and gives `beBkt γ bi`;
   4a's `MvccStorage.lean` uses `schemaBkts` (your `Bkt` table) with `schemaBkts_ok`.
2. **`Backend.safeRegOk`** (the registry `safeRangeBucketNames` names only safe-range buckets: what a
   non-blocking defragmentation's catch-up needs; `New` takes it when configured non-blocking):
   introduced by your package's initialization (`bucket.go:64` registers exactly the
   `safeRangeBucket` ones). A law of your `init` once 4a's predicate gets its realization over the
   variable (a recorded gap).
3. Still open from "from 4a": your `txWr` put row needs the entry bound; your read-transaction
   `UnsafeForEach` is two sorted runs (`rdOrder`), not key order. And on a **concurrent** read
   transaction (none of yours: you use `ReadTx`), reads are single-key with lingering deletes
   (`lingerSingle`).
4. Range results are now lent (`Backend.rangeRes`: back to the transaction resource), as your
   round 1's `rangeK`/`lentIn`.
5. The hooks' footprint `Fh` (`hookOk γ hk Fh Pk`): the server's hooks (2e) write `meta`'s
   `consistent_index`, `term`, `confState`; they must be puts only, and tracked through an invariant
   the hooks' update opens (not the lock's resource) if anyone reads them through `ReadTx`.
