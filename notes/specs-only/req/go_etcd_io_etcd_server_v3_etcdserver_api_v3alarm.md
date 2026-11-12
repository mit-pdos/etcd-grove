# Requirements on `go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm` (2e)


## from 3a

The apply layer (3a) holds the alarm store's view on the apply thread (`alarmSt γa σ.alarms`
inside `Apply.smAt`) and calls `Get` (`restoreAlarms`, the backend's `GET`), `Activate` and
`Deactivate` (the backend's `Alarm`):
1. `Deactivate(id, at)` for a type with no kind (`NONE`, another value): `nil` (absent), no panic.
2. **The request path reads the view concurrently** (`EtcdServer.Alarms()`, the NOSPACE check of
   `applyEntryNormal`): a split of `alarmSt` (the apply thread the only writer, readers' atomic
   updates fired at the current view), or a law from 2d's invariant; 3a's `smAt` owns the writer's
   part.
Used by: `applierV3backend.Alarm.spec`, `uberApplier.restoreAlarms.spec`.


## from 3a (round 1)

3. W0's `AlarmKind` now has `other n`: `kindOf` should map every type but `NONE` (so `Activate` of an
   unknown type, which an administrator can propose and Go stores, has a spec and 3a's `IrrOp.ok`
   can drop its known-kind premise).

## from 4b

`alarmBe ab al` is `∃ lg be, ab = alarmBackend{lg, be} (read-only) ∗ Schema.alarmBkt be (some al)`;
the methods' specs are `Schema.alarmBackend.*.spec` (assumed: names only). `MustPutAlarm`/
`MustDeleteAlarm` run the backend's post-lock hook (`LockInsideApply`): they take
`Schema.applyHook be Pre Q ∗ Pre` (the apply thread's hook pre, 2d) and give `Q`. `GetAllAlarms`
takes and gives back the caller's `threadTok` (its read transaction's reader slot); the alarms come
as fresh `AlarmMember` messages with `Schema.alarmMemberIs`, a permutation of `al`, error `nil`.
`CreateAlarmBucket` turns `alarmBkt be none` (no bucket) into `alarmBkt be (some [])`.
