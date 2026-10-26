---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#19328 pr merged: related, not this bug: renamed `experimental-downgrade-check-time` to `downgrade-check-time`, no validation added
  - etcd-io/etcd#22476 pr open: related, not this bug: replaces `monitorDowngrade`'s `time.After(t)` by `time.NewTicker(t)` after the `t == 0` check, so merged as is a negative value panics at startup instead of spinning (as `etcd-corrupt-check-time-negative-panic`)
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
- **Upstream change in flight**: etcd-io/etcd#22476 (open, unreviewed, 2026-09-25) replaces the
  loop's `time.After(t)` by a `time.NewTicker(t)` after the `t == 0` check; merged as is, a negative
  value panics at startup instead of spinning, as
  [etcd-corrupt-check-time-negative-panic](etcd-corrupt-check-time-negative-panic.md). Rechecked on
  `main` `f3221acd1` (2026-10-26), and `<-time.After(-1s)` returns at once (a Go 1.27 program: about
  87,500 iterations in 100 ms).
- **Possible fixes**: in `Config.Validate`, reject `DowngradeCheckTime < 0`. Could go in one PR
  with [etcd-corrupt-check-time-negative-panic](etcd-corrupt-check-time-negative-panic.md) and
  [etcd-compaction-negative-batch-limit](etcd-compaction-negative-batch-limit.md).
- **Found**: 2026-10-23, surveying etcd's flag validation for
  `etcd-compaction-negative-batch-limit` (review of `issues/INDEX-reviewed.md`).
