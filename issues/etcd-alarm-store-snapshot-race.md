---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/etcd#22609 pr merged: the same class (mvcc `Hash` racing with `Restore`'s backend swap); a different field
  - etcd-io/etcd#10874 pr closed: `s.be` read outside `bemu` in `applySnapshot`; not the alarm store
candidate: issues/upstream/etcd-alarm-store-snapshot-race/
---

# `applySnapshot` replaces `s.alarmStore` while gRPC and health goroutines read it (a data race)

- **Status**: a bug: a data race (Go memory model) between the apply goroutine and every reader of
  `EtcdServer.Alarms()`, reported by the race detector in normal operation (a follower installs a
  leader's snapshot while a client calls `Maintenance/Status`). Reproduced (below). The observable
  effect is small: during the window a reader can see the old alarm store (the alarms from before
  the snapshot) or, with no happens-before edge to `NewAlarmStore`'s initialization, a store whose
  fields it sees partly initialized (an empty alarm map: no alarm). So `Status` and the `/health`
  checks can report a stale or empty alarm list for that moment. No crash found. The race itself
  is the bug: etcd's tests run with `-race`, and the code has no synchronization at all here.
- **Where** (the etcd fork's `goose-lean` at `de825d8c6`, where this was found; the same code at the pin of `etc/goose.py`, `2aed163b1`; upstream `main` has the same code):
  - `server/etcdserver/server.go:2409-2416` (`restoreAlarms`): `s.alarmStore = as`, with no lock,
    called by `applySnapshot` (`server.go:1102`) on the apply goroutine after `s.bemu.Unlock()`.
  - `server/etcdserver/server.go:2440-2442` (`Alarms`): `return s.alarmStore.Get(...)`, with no lock.
    It is called from other goroutines: `v3rpc/maintenance.go:301` (`maintenanceServer.Status`),
    `api/etcdhttp/health.go:186` (`checkAlarms`, the `/health` handler) and `:422`
    (`activeAlarmCheck`, `/livez`/`/readyz`).
  - (`server.go:1991`, `s.alarmStore.Get(pb.AlarmType_NOSPACE)` in `apply`, runs on the apply
    goroutine itself: no race.)
- **What happens**: reproduction `issues/etcd-alarm-store-snapshot-race/repro_test.go`: copy it into
  `tests/integration/` and run `go test -race ./integration -run TestV3AlarmsDuringSnapshotInstall
  -count=1 -v` from `tests/` (Go 1.27.1). Three members, `SnapshotCount: 10`,
  `SnapshotCatchUpEntries: 5`; a follower is cut off, the leader takes 40 puts, eight goroutines
  call `Status` on the follower, and the partition heals; the test checks that the follower
  installed a snapshot (`Server.Backend()` changed). At the pin, 4 of 5 runs fail with `race
  detected during execution of test`: `Write at ... (*EtcdServer).restoreAlarms() server.go:2414 ←
  applySnapshot server.go:1102` against `Previous read at ... (*EtcdServer).Alarms() server.go:2441
  ← (*maintenanceServer).Status() maintenance.go:301`. (The fifth installed the snapshot without
  the race being caught.)
- **Expected**: installing a snapshot is internal to the member; `Alarms()` returns the alarms of
  the store before or after the swap, with the read synchronized with the write.
- **How the proof handles it**: not reached today. The server's persistent invariants hold the
  field read-only for good (`srvAlarmStoreAddr s ↦□`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvApplier.lean:489`, `InvBuild.lean:243`,
  `InvStart.lean:77`), which is true while no member installs a snapshot (`applySnapshot`'s spec
  covers only the empty snapshot, `bootOk`'s `"%Hnosnap"`); `EtcdServer.Alarms` is not verified.
  `restoreAlarms`'s own spec takes the field owned (`Spec/.../EtcdServer__restoreAlarms.lean`).
  Stage S-j2 of track T-S (`notes/decisions.md`, "D22 S-j2 carried out") found it: the snapshot
  path must give the field to the apply thread, and then no concurrent reader can be verified
  (Perennial's semantics make a racy load undefined), so a verified `Alarms` needs the fix.
- **Possible fixes**: (1) hold the alarm store in an `atomic.Pointer[v3alarm.AlarmStore]`
  (`restoreAlarms` stores, `Alarms`, `NewUberApplier` and `apply` load); or (2) swap it under
  `s.bemu` (build the new store before `s.bemu.Unlock()`, assign it inside the critical section, and
  have `Alarms()` read the field under `s.bemu.RLock()`), at the cost of holding `bemu` across
  `NewAlarmStore`'s `ForceCommit`.
- **Fix chosen upstream** (2026-10-21, `issues/upstream/etcd-alarm-store-snapshot-race/`): neither of the
  above: `AlarmStore.Recover(be)` reloads the store in place under its own mutex, as `lessor.Recover` does, and
  `applySnapshot` calls it instead of `restoreAlarms`, so `s.alarmStore` is written only by `NewServer` (the
  comparison is in the candidate's `meta.md`; branch rebuilt 2026-10-23 off `main` 3aaab3479, fix 7569d2bbd). For the proof this makes the field read-only for good again
  (`srvAlarmStoreAddr s ↦□` holds through the snapshot path); `Recover` needs a spec on the store's lock invariant.
- **Fixed in the fork** (2026-10-22, `goose-lean` `8fd98af04`, under `188113160`, the pin of
  `etc/goose.py`): the upstream candidate's fix (`d396a0fc7`, `AlarmStore.Recover` called by
  `applySnapshot`, the two unit tests given an alarm store) with its test `TestV3AlarmsDuringSnapshotInstall`
  (`tests/integration/v3_alarm_test.go`) in one commit. With `-race`, the test fails 5 of 5 without
  the fix (two or three `DATA RACE` reports each: `restoreAlarms` against `Alarms`, and `Get` against
  `NewAlarmStore`'s initialization) and passes 15 of 15 with it.
- **Found**: 2026-10-20, stage S-j2 of track T-S, listing the server fields `applySnapshot` writes
  against the proof's read-only facts of them.
