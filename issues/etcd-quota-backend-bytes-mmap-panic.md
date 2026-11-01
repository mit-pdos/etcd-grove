---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: yes
---

# etcd: a `--quota-backend-bytes` above about 230 TiB crashes etcd at startup with "mmap too large"

etcd accepts any positive `--quota-backend-bytes`, but it maps 110% of the quota when it opens its
database, and bbolt refuses a mapping above 256 TiB (amd64, arm64; less on 32-bit platforms), so a
larger quota makes etcd panic at startup with `failed to open database` and `mmap too large`, a
message that does not name the flag.

**Expected:** etcd should reject the value at startup with an error naming the flag and its
maximum, or document the limit; the flag's help ("Sets the maximum size (in bytes) that the etcd
backend database may consume. ... Set to 0 to use the default 2GiB limit.") states none, and
[`Config.Validate`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/embed/config.go#L926)
already rejects other unusable values with such errors.

**Impact:** an operator's absurd setting (the recommended maximum is 8 GiB, above which etcd only
warns); the failure is immediate and loud. Every release.

**Reproduction:** `TestLargeQuotaBackendBytesFlag` in
[`issues/etcd-quota-backend-bytes-mmap-panic/quota_flag_test.go`](etcd-quota-backend-bytes-mmap-panic/quota_flag_test.go),
copied into `server/embed` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28),
go1.27.3 linux/amd64. It parses `--quota-backend-bytes=1125899906842624` (1 PiB) with etcd's own
flag set (`Config.AddFlags`, as `etcdmain` does) and starts a single member with `StartEtcd`, in a
child process:

```
$ go test ./embed -run TestLargeQuotaBackendBytesFlag -count=1
--- FAIL: TestLargeQuotaBackendBytesFlag (0.04s)
    zz_quota_test.go:50: etcd with --quota-backend-bytes=1125899906842624 crashed (exit status 2): panic: failed to open database

        goroutine 117 [running]:
        go.uber.org/zap/zapcore.CheckWriteAction.OnWrite(0x2?, 0x398af4cd75f0?, {0x0?, 0x0?, 0x398af4e98320?})
FAIL	go.etcd.io/etcd/server/v3/embed	0.091s
```

**Cause:** [`newBackend`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/storage/backend.go#L53-L56)
sets the initial mmap size to `q + q/10` for a quota `q`, which bbolt v1.5.0's `Open` refuses above
its `maxMapSize`, and the backend
[panics](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/storage/backend/backend.go#L225-L236)
on the error. (A `q` with `q + q/10` above `MaxInt64` overflows there too.)

## Proof

yes: `storage.OpenBackend`'s trust-boundary axiom needed the premise `openMmapOk cfg` (the quota
not positive, the default, or `q + q/10 ≤ 0xFFFFFFFFFFFF`;
`Proof/go_etcd_io/etcd/server/v3/storage/InvOpen.lean`), which `NewServer.spec` takes and etcd does
not check; found by the `axiom` skill (`notes/axiom-review/openbackend.md`).

## Fix

`Config.Validate` rejects a quota whose mapping would exceed bbolt's maximum (or `newBackend`
clamps the mapping), and the flag's help states the limit.
