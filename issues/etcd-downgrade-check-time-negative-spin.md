---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#19328 pr merged: related, not this bug: renamed `experimental-downgrade-check-time` to `downgrade-check-time`, no validation added
  - etcd-io/etcd#22476 pr closed: related, not this bug: replaced `monitorDowngrade`'s `time.After(t)` by `time.NewTicker(t)`, which would have turned this spin into a startup panic; closed unmerged
blocks-proof: no
---

# etcd: a negative `--downgrade-check-time` makes an idle member use a full CPU core

`etcd --downgrade-check-time=-1s` is accepted, and the member's downgrade monitor then loops
without pause for the member's lifetime: an idle single-member cluster uses a whole core (on the
leader, each iteration also reads the cluster's versions). The flag's value is not validated.

**Expected:** etcd should reject the value at startup with an error naming the flag, as it does for
the comparable [`--compact-hash-check-time`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/embed/config.go#L1022-L1024)
(`must be >0`); the flag's help, "Duration of time between two downgrade status checks.", gives no
other meaning to a negative value.

**Impact:** a misconfiguration only (a typo or a templating error); silent apart from the CPU use.
Every release with the flag (named `--experimental-downgrade-check-time` before #19328).

**Reproduction:** `TestNegativeDowngradeCheckTimeFlag` in
[`issues/etcd-downgrade-check-time-negative-spin/downgrade_check_time_test.go`](etcd-downgrade-check-time-negative-spin/downgrade_check_time_test.go),
copied into `server/embed` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28),
go1.27.3 linux/amd64. It parses `--downgrade-check-time=-1s` with etcd's own flag set
(`Config.AddFlags`, as `etcdmain` does), starts a single member with `StartEtcd` and measures the
process's CPU time over two idle seconds (with `--downgrade-check-time=5s`, the default, the same
test measures 14ms and passes):

```
$ go test ./embed -run TestNegativeDowngradeCheckTimeFlag -count=1 -v
=== RUN   TestNegativeDowngradeCheckTimeFlag
    zz_downgrade_test.go:54: CPU time of the idle member over 2s: 2.211343s
    zz_downgrade_test.go:56: an idle member with --downgrade-check-time=-1s used 2.211343s of CPU in 2s
--- FAIL: TestNegativeDowngradeCheckTimeFlag (4.10s)
FAIL	go.etcd.io/etcd/server/v3/embed	4.213s
```

**Cause:** [`Start`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L544)
always runs [`monitorDowngrade`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L2332-L2350),
which returns only for `DowngradeCheckTime == 0` and otherwise waits on `time.After(t)`, which
fires at once for a negative `t`; `Config.Validate` does not check the field.

## Proof

no: outside the verified code.

## Fix

`Config.Validate` rejects a negative `DowngradeCheckTime`; one validation PR could cover
`--corrupt-check-time` (etcd-corrupt-check-time-negative-panic) and `--compaction-batch-limit`
(etcd-compaction-negative-batch-limit) too.

## Notes

Found by code reading (2026-10-23); the test was written 2026-11-01. It reads the CPU time with
`getrusage` (Linux build tag).
