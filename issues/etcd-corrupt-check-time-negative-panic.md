---
upstream: unchecked
checked: 2026-10-23
links: []
---

# A negative `--corrupt-check-time` panics the member at startup

- **Status**: a bug (a reachable panic from an unvalidated flag; a misconfiguration, low
  severity). Found by code reading, not reproduced.
- **Where**: etcd upstream `main` at `3aaab3479`. `EtcdServer.Start` starts `monitorKVHash`
  unconditionally (`server/etcdserver/server.go:542`); `monitorKVHash` returns only for
  `CorruptCheckTime == 0` and otherwise calls `time.NewTicker(t)` (`server.go:2245-2249`), which
  panics for `t < 0` ("non-positive interval for NewTicker"). The flag
  (`server/embed/config.go:736`, "Duration of time between cluster corruption check passes.") is
  not checked by `Config.Validate` (`config.go:926-1058`), which rejects the comparable
  `--compact-hash-check-time <= 0` (`config.go:1022-1024`).
- **What happens**: `etcd --corrupt-check-time=-1s` starts, then the goroutine's panic exits the
  process.
- **Expected**: the flag rejected at startup with an error, as `--compact-hash-check-time` is.
- **How the proof handles it**: outside the verified code (the server's monitors are not
  verified).
- **Possible fixes**: in `Config.Validate`, reject `CorruptCheckTime < 0`; or treat `<= 0` as
  disabled in `monitorKVHash`. Could go in one PR with the validation of
  [etcd-compaction-negative-batch-limit](etcd-compaction-negative-batch-limit.md) and
  [etcd-downgrade-check-time-negative-spin](etcd-downgrade-check-time-negative-spin.md).
- **Found**: 2026-10-23, surveying etcd's flag validation for
  `etcd-compaction-negative-batch-limit` (review of `issues/INDEX-reviewed.md`).
