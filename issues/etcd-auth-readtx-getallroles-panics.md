---
upstream: unchecked
checked: 2026-10-23
links: []
---

# etcd: `(*authReadTx).UnsafeGetAllRoles` always panics on a read transaction

- **Status**: an unusable API method (a reachable panic through the `auth.AuthReadTx` interface,
  not reached by etcd itself: no caller today). `authReadTx.UnsafeGetAllRoles` ranges the
  `authRoles` bucket with no limit through a `backend.ReadTx`, whose `UnsafeRange` panics on a
  range of more than one key of a bucket that is not the key bucket. Only the batch transaction's
  `UnsafeRange` (which the `authBatchTx` twin uses) permits it.
- **Where** (etcd `goose-lean` `188113160`, the same code upstream):
  `server/storage/schema/auth_roles.go:86-96`: `(*authReadTx).UnsafeGetAllRoles` calls
  `unsafeGetAllRoles(atx.lg, atx.tx)`, which does `tx.UnsafeRange(AuthRoles, []byte{0},
  []byte{0xff}, -1)`; `server/storage/backend/read_tx.go:78-88`: `baseReadTx.UnsafeRange` turns
  `limit <= 0` into `math.MaxInt64` and panics (`"do not use unsafeRange on non-keys bucket"`)
  when `limit > 1 && !bucketType.IsSafeRangeBucket()`; `server/storage/schema/bucket.go`: only
  `Key` is a safe-range bucket (`AuthRoles` is `bucket{22, authRolesBucketName, false}`).
  `batchTx.UnsafeRange` (`batch_tx.go:194-204`) has no such check, so
  `(*authBatchTx).UnsafeGetAllRoles`, the one `GetAllRoles` (`auth_roles.go:40-45`) uses, works.
- **What happens**: any call of `UnsafeGetAllRoles` on the `AuthReadTx` that
  `AuthBackend.ReadTx()` returns panics, locked or not. etcd never makes one: the auth store's
  `GetAllRoles` goes through `as.be.GetAllRoles()` (`server/auth/store.go:677`), the batch
  transaction; the read transaction's `UnsafeGetAllUsers` (a `UnsafeForEach`) is fine. A test:

  ```go
  be, _ := betesting.NewDefaultTmpBackend(t)   // server/storage/backend/testing
  ab := schema.NewAuthBackend(zaptest.NewLogger(t), be)
  ab.CreateAuthBuckets()
  tx := ab.ReadTx()
  tx.RLock()
  defer tx.RUnlock()
  tx.UnsafeGetAllRoles()   // panics: "do not use unsafeRange on non-keys bucket"
  ```
- **Expected**: `AuthReadTx`'s documentation (`server/auth/store.go:212-224`) presents
  `UnsafeGetAllRoles` as one of the transaction's reads, like `UnsafeGetAllUsers`; nothing says it
  may not be called on a read transaction.
- **How the proof handles it**: the auth backend's read side is proved over the read
  transaction's point reads only (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`,
  `authPointSpec`: `UnsafeRange(b, key, nil, 0)`); `unsafeGetAllRoles` and
  `authReadTx.UnsafeGetAllRoles` are translated and not specified (the server's link file,
  `etc/link-lean-first-server.txt`, says so). The backend's `readTx.UnsafeRange` spec has the
  panic as a premise (`sint.Z (rangeLimit eb limit) ≤ 1 ∨ bi.safe = true`,
  `Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__UnsafeRange.lean`).
- **Possible fixes**: make `unsafeGetAllRoles` iterate with `UnsafeForEach` as
  `unsafeGetAllUsers` does (then both transactions can serve it), or drop `UnsafeGetAllRoles` from
  `AuthReadTx` (keep it on `AuthBatchTx`).
- **Found**: 2026-10-23, specifying schema's auth backend (the auth plan's S1,
  `notes/auth-plan.md`): the read transaction's spec refuses the range read.
