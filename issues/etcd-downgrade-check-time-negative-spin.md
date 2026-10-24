---
upstream: unchecked
checked: 2026-10-23
links: []
---

# A negative `--downgrade-check-time` makes the downgrade monitor spin

- **Status**: a bug (an unvalidated flag making a background loop spin; a misconfiguration, low
  severity). Found by code reading, not reproduced.
- **Where**: etcd upstream `main` at `3aaab3479`. `EtcdServer.Start` starts `monitorDowngrade`
  unconditionally (`server/etcdserver/server.go:544`); it returns only for
  `DowngradeCheckTime == 0` and otherwise loops on `time.After(t)` (`server.go:2332-2350`), which
  fires at once for `t < 0`, so the loop runs without pause, and on the leader calls
  `CancelDowngradeIfNeeded` every iteration. The flag (`server/embed/config.go:742`) is not checked
  by `Config.Validate`, which rejects the comparable `--compact-hash-check-time <= 0` for exactly
  this reason (`config.go:1022-1024`).
- **What happens**: `etcd --downgrade-check-time=-1s` burns a core for the member's lifetime
  (and, on the leader, reads the cluster's versions in a tight loop).
- **Expected**: the flag rejected at startup with an error, as `--compact-hash-check-time` is.
- **How the proof handles it**: outside the verified code.
- **Possible fixes**: in `Config.Validate`, reject `DowngradeCheckTime < 0`. Could go in one PR
  with [etcd-corrupt-check-time-negative-panic](etcd-corrupt-check-time-negative-panic.md) and
  [etcd-compaction-negative-batch-limit](etcd-compaction-negative-batch-limit.md).
- **Found**: 2026-10-23, surveying etcd's flag validation for
  `etcd-compaction-negative-batch-limit` (review of `issues/INDEX-reviewed.md`).
