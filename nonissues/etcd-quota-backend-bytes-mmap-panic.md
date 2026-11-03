---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# etcd: a `--quota-backend-bytes` above about 90 TiB crashes etcd at startup with "failed to open database"

etcd accepts any positive `--quota-backend-bytes`, but it maps 110% of the quota when it opens its
database, in one `mmap`. A mapping larger than the process's free address space (about 105 TiB on
amd64 Linux, out of 128 TiB) fails with `cannot allocate memory`, and bbolt refuses one above 256 TiB
(amd64, arm64; less on 32-bit platforms) with `mmap too large`; either way etcd panics at startup with
`failed to open database`, a message that does not name the flag.

**Why not an issue:** an absurd configuration (a `--quota-backend-bytes` above about 90 TiB): the proof takes a precondition on it rather than a fix (the user's call, 2026-11-02).

**Expected:** etcd should reject the value at startup with an error naming the flag and its
maximum, or document the limit; the flag's help ("Sets the maximum size (in bytes) that the etcd
backend database may consume. ... Set to 0 to use the default 2GiB limit.") states none, and
[`Config.Validate`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/embed/config.go#L926)
already rejects other unusable values with such errors.

**Impact:** an operator's absurd setting (the recommended maximum is 8 GiB, above which etcd only
warns); the failure is immediate and loud. Every release.

**Reproduction:** `TestLargeQuotaBackendBytesFlag` in
[`nonissues/etcd-quota-backend-bytes-mmap-panic/quota_flag_test.go`](etcd-quota-backend-bytes-mmap-panic/quota_flag_test.go),
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
on the error. bbolt maps the whole size with one
[`mmap(2)`](https://github.com/etcd-io/bbolt/blob/e7a8b2dd498494a3766ba24dd94d3509e5588485/bolt_unix.go#L57),
so below `maxMapSize` the limit is the address space: `q = 2^47` (`q + q/10` = 140.8 TiB) fails with
`mmap failed, size: 154812096184320, error: cannot allocate memory`, while `q + q/10` = 64 TiB opens
(measured in a Go test process; the limit depends on the process's other mappings and `RLIMIT_AS`). (A
`q` with `q + q/10` above `MaxInt64` overflows there too.)

## Proof

no: a precondition on the configuration, which the top-level adequacy proof takes, not a fix on the goosed fork; `storage.OpenBackend`'s trust-boundary axiom needed the premise `openMmapOk cfg` (the quota
not positive, the default, or `q + q/10 ≤ 0xFFFFFFFFFFFF`;
`Proof/go_etcd_io/etcd/server/v3/storage/InvOpen.lean`), which `NewServer.spec` takes and etcd does
not check; found by the `axiom` skill (`notes/axiom-review/openbackend.md`). That bound is still
bbolt's `maxMapSize`, so it does not exclude the address-space failure: the axiom's second review
(`notes/axiom-review/openbackend-post.md`, branch `axiom/openbackend-post`, `examples/axiomcx/openva`)
proposes `q + q/10 ≤ 2^46`.

## Fix

`Config.Validate` rejects a quota whose mapping the address space cannot hold (bbolt's maximum,
`maxMapSize·10/11`, still fails on amd64 Linux), with an error naming the flag, and the `int64`
overflow; or `newBackend` clamps the initial mapping to one the process can map (bbolt grows the map
as the file grows, and the quota alarm still applies); and the flag's help states the limit.
