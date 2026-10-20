---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/etcd#13084 pr merged: same crash (ACTIVATE with no alarm type: empty key, unsafePut's Fatal in AlarmStore.Activate, found by fuzzing the gateway), fixed only in the caller (the applier's AlarmType_NONE skip this finding cites); Activate itself still unguarded and undocumented
---

# `AlarmStore.Activate(0, AlarmType_NONE)` makes the backend exit the process

- **Status**: an unstated precondition of an exported method; unreachable from etcd's own code
  (the applier skips `ACTIVATE` with `AlarmType_NONE`).
- **Where**: at the etcd pin of `etc/goose.py` (`09669450f`): `server/etcdserver/api/v3alarm/
  alarms.go` (`AlarmStore.Activate` puts `newAlarm` through `MustPutAlarm`);
  `server/storage/schema/alarm.go` (`mustUnsafePutAlarm`: the key is `proto.Marshal(alarm)`, the
  value nil); `server/storage/backend/batch_tx.go:169` (`unsafePut`: `lg.Fatal` on any error of
  bbolt's `Put`); the caller `server/etcdserver/apply/backend.go:115-119`
  (`applierV3backend.Alarm`: `if ar.Alarm == pb.AlarmType_NONE { break }` before `Activate`).
- **What happens**: `Activate(0, AlarmType_NONE)` builds `AlarmMember{MemberID: 0, Alarm: NONE}`,
  both fields at their zero values, whose encoding is empty; bbolt's `Put` refuses an empty key
  (`ErrKeyRequired`) and the backend's `Fatal` exits the process. Any other pair encodes to a
  non-empty key. Not reproduced (by reading: proto3 encodes no zero-valued scalar field).
- **Expected**: `Activate`'s documentation to say that the alarm type must not be `NONE` (as its
  only caller ensures), or `Activate` to ignore `NONE`.
- **How the proof handles it**: the apply package's contract of the alarm store
  (`apply.isAlarmStore`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Contracts.lean`) is to
  take the type `at' ≠ 0` in `Activate`'s clause (what `applierV3backend.Alarm`'s proof has at the
  call) when it becomes `v3alarm.NewAlarmStore`'s axiom (unit N4, 2026-10-17).
- **Possible fixes**: `if at == pb.AlarmType_NONE { return nil }` at the top of `Activate`, or a
  documentation line.
- **Found**: 2026-10-17, writing `v3alarm.NewAlarmStore`'s contract as an axiom true of the Go code
  (unit N4, D14d).
