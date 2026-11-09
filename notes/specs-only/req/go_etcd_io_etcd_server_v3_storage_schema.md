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
   batch transaction of `be` whose lock is held (`beApplyTok`'s `LockInsideApply`, `beTxHeld`, or
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
