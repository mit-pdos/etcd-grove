---
upstream: unchecked
---

# A `--quota-backend-bytes` above about 2.5·10^14 (amd64) makes etcd panic at startup ("mmap too large")

- **Status**: an unstated precondition. etcd's configuration accepts any positive
  `QuotaBackendBytes` (the flag's help says only "Sets the maximum size (in bytes) that the etcd
  backend database may consume"). But the backend maps 110% of it up front, and bbolt refuses a map
  above its `maxMapSize`, so the server panics while opening its database. There is no validation
  and no documented limit. Low severity: it needs an absurd quota, an operator's mistake, not a
  client's, and the failure is immediate and loud. But the panic message ("failed to open
  database ... mmap too large") does not point at the flag.
- **Where** (the fork's `249d76bea`, `etc/goose.py`'s pin; upstream `main` has the same code):
  - `server/storage/backend.go:53-56` (`newBackend`): for a quota `q > 0` other than
    `DefaultQuotaBytes` (2 GiB), `bcfg.MmapSize = uint64(q + q/10)` ("permit 10% excess over quota
    for disarm").
  - `server/storage/backend/backend.go:225`: `bopts.InitialMmapSize = bcfg.mmapSize()`, passed to
    `bolt.Open` (`:233`).
  - bbolt v1.5.0 `db.go:590` (`mmapSize`): `if size > common.MaxMapSize { return 0, errors.New("mmap
    too large") }`; `MaxMapSize` is `0xFFFFFFFFFFFF` (256 TiB) on amd64 and arm64, smaller on 32-bit
    platforms.
  - `server/storage/backend/backend.go:235`: `bcfg.Logger.Panic("failed to open database", ...)`, on
    `OpenBackend`'s goroutine (`server/storage/backend.go`), so the process dies.
  - `server/embed/config.go:616`: the flag's documentation, with no upper bound. `quota.go` only
    warns above the recommended `MaxQuotaBytes` (8 GiB).
  - A `q` with `q + q/10` above `MaxInt64` overflows in `newBackend` too.
- **What happens**: reproduction `issues/etcd-quota-backend-bytes-mmap-panic/repro_test.go`. Copy it
  into `server/storage/` and run `go test ./storage -run 'TestOpenBackend(Large|Default)Quota' -v` from
  `server/`. With `QuotaBackendBytes: 1 << 50` the child process dies with `panic: failed to open
  database` and bbolt's `mmap too large`. The control, with the default quota in the same
  environment, opens. Run at the pin (go1.27.3, amd64):

  ```
  --- PASS: TestOpenBackendLargeQuota (0.01s)
      quota_repro_test.go:52: the child panicked (exit status 2)
  --- PASS: TestOpenBackendDefaultQuota (0.00s)
  ```
- **Expected**: the configuration is rejected at validation with a message naming the flag and its
  maximum, or the documentation states the limit.
- **How the proof handles it**: `storage.OpenBackend`'s axiom takes `openPre`, which now includes
  `openMmapOk cfg` (`Proof/go_etcd_io/etcd/server/v3/storage/InvOpen.lean`): the quota is not
  positive, is the default, or `q + q/10 ≤ 0xFFFFFFFFFFFF`. `NewServer.spec`, `specCompact` and
  `specM` take it as a premise (`"%Hmmap"`), and the examples discharge it with their default quota.
  The `axiom` skill found the gap: `notes/axiom-review/openbackend.md` (the counterexample on branch
  `axiom/openbackend`, `examples/axiomcx/openquota`).
- **Possible fixes**: validate `QuotaBackendBytes` in `embed.Config.Validate` (or in
  `newBackend`) against `MaxMapSize·10/11` and the `int64` overflow, with a clear error; or clamp
  the mmap size to bbolt's maximum (the quota alarm still applies); and document the limit in the
  flag's help.
- **Found**: 2026-10-29, by the `axiom` skill's review of `storage.OpenBackend`
  (`notes/axiom-review/openbackend.md`).
