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
