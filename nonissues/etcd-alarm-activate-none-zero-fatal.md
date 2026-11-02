---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#13084 pr merged: same crash (ACTIVATE with no alarm type: empty key, unsafePut's Fatal in AlarmStore.Activate, found by fuzzing the gateway), fixed only in the caller (the applier's AlarmType_NONE skip); Activate itself still unguarded and undocumented
blocks-proof: no
---

# v3alarm: `AlarmStore.Activate(0, AlarmType_NONE)` makes the backend exit the process

`Activate(0, NONE)` stores `AlarmMember{MemberID: 0, Alarm: NONE}`, whose protobuf encoding (the
bbolt key) is empty; bbolt refuses an empty key and the backend's `Fatal` exits the process.

**Why not an issue:** a precondition etcd meets: its only caller, `applierV3backend.Alarm`, skips
`ACTIVATE` with `AlarmType_NONE` (the caller-side fix of #13084). No test, found by code reading.

## Proof

no: the alarm store's contract (`apply.isAlarmStore`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Contracts.lean`) takes the type `≠ NONE` in
`Activate`'s clause, which the applier meets.

## Notes

The 2026-10-23 review's plan: skip for now.
