---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#21986 issue open: same bug (merge's no-overlap fast path skips dedupe; a single-key read returns the older value)
  - etcd-io/etcd#21987 pr open: fix for #21986 (dedupe intra-batch duplicates in writeback before merge); the verified fork carries it
  - etcd-io/etcd#22298 pr open: same fix (dedupe on every writeback path into an existing read bucket), filed as hardening without an issue
  - etcd-io/etcd#21985 pr closed: earlier fix attempt for the same bug (dedupe on the merge path), superseded by #21987
blocks-proof: yes
---

# backend: after two puts of one key in one write session, reads return the older value until the next commit

When a batch transaction puts the same key twice before unlocking, and the bucket's read-buffer entry
survived the previous commit, the read buffer keeps both values and `ReadTx`/`ConcurrentReadTx` return
the older one, while the batch transaction (and bbolt) has the newer one, until the next commit
(at most the batch interval, 100 ms by default). etcd reaches it in the storage-version migration
from v3.5 to v3.7 (`monitorStorageVersion` → `UnsafeMigrate` under one `LockOutsideApply` session,
which puts `meta/storageVersion` three times): `EtcdServer.StorageVersion()` then reports 3.5.0 for
up to a batch interval, and the monitor migrates again.

**Reproduction:** `TestMigrateStaleRead` in
[`issues/etcd-backend-duplicate-put-stale-read/migrate_stale_read_test.go`](etcd-backend-duplicate-put-stale-read/migrate_stale_read_test.go),
copied (as `zz_migrate_stale_read_test.go`) into `server/storage/schema` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef
(2026-10-28), go1.27.3:

```
$ (cd server && go test ./storage/schema -run '^TestMigrateStaleRead$' -count=1)
--- FAIL: TestMigrateStaleRead (0.01s)
    zz_migrate_stale_read_test.go:54: ReadTx: 3.5.0 (err <nil>); BatchTx: 3.7.0
FAIL
```

## Proof

yes: the verified fork carries etcd-io/etcd#21987 (`goose-lean` `ea78ec948`); before it the write
buffer's spec needed distinct keys per session, which the migration breaks
(`Spec/go_etcd_io/etcd/server/v3/storage/backend/txWriteBuffer__writeback.lean`).

## Notes

The backend-level form (two `UnsafePut`s of `foo`, then `ReadTx` reads `v2`, `BatchTx` `v3`) is
what #21986 reports; the test here goes through the migration, etcd's caller.
