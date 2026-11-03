---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#19156 pr merged: related, not this bug: renamed `experimental-corrupt-check-time` to `corrupt-check-time`, no validation added
blocks-proof: no
---

# etcd: a negative `--corrupt-check-time` crashes the member right after it starts

`etcd --corrupt-check-time=-1s` is accepted: the member starts, and its corruption-check
goroutine then panics with `non-positive interval for NewTicker`, ending the process. The flag's
value is not validated at startup.

**Why not an issue:** an absurd configuration (a negative `--corrupt-check-time`): the proof takes a precondition on it rather than a fix (the user's call, 2026-11-02).

**Expected:** etcd should reject the value at startup with an error naming the flag, as it does for
the comparable [`--compact-hash-check-time`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/embed/config.go#L1022-L1024)
(`must be >0`); the flag's help, "Duration of time between cluster corruption check passes.",
gives no other meaning to a negative value.

**Impact:** a misconfiguration only (a typo or a templating error in the flag or the config
file); the failure is immediate and loud, but the panic message does not name the flag. Every
release with the flag (named `--experimental-corrupt-check-time` before #19156).

**Reproduction:** `TestNegativeCorruptCheckTimeFlag` in
[`nonissues/etcd-corrupt-check-time-negative-panic/corrupt_check_time_test.go`](etcd-corrupt-check-time-negative-panic/corrupt_check_time_test.go),
copied into `server/embed` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28),
go1.27.3 linux/amd64. It parses `--corrupt-check-time=-1s` with etcd's own flag set
(`Config.AddFlags`, as `etcdmain` does) and starts a single member with `StartEtcd`, in a child
process:

```
$ go test ./embed -run TestNegativeCorruptCheckTimeFlag -count=1
--- FAIL: TestNegativeCorruptCheckTimeFlag (0.20s)
    zz_corrupt_test.go:51: etcd with --corrupt-check-time=-1s crashed (exit status 2): panic: non-positive interval for NewTicker

        goroutine 234 [running]:
        time.NewTicker(0x0?)
        	/usr/local/go/src/time/tick.go:38 +0x9e
        go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).monitorKVHash(0x3f
FAIL	go.etcd.io/etcd/server/v3/embed	0.232s
```

**Cause:** [`Start`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L542)
always runs [`monitorKVHash`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L2244-L2249),
which returns only for `CorruptCheckTime == 0` and otherwise calls `time.NewTicker`, which panics on
a negative interval; `Config.Validate` does not check the field.

## Proof

no: a precondition on the configuration, which the top-level adequacy proof takes, not a fix on the goosed fork; outside the verified code (the server's monitors are not verified).

## Fix

`Config.Validate` rejects a negative `CorruptCheckTime`; one validation PR could cover
`--downgrade-check-time` (etcd-downgrade-check-time-negative-spin) and
`--compaction-batch-limit` (etcd-compaction-negative-batch-limit) too.

## Notes

Found by code reading (2026-10-23); the test was written 2026-11-01.
