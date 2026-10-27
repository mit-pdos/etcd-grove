---
upstream: unchecked
links: []
---

# A bucket handle used after its bucket is deleted panics or silently misses the data

- **Status**: documentation the code contradicts (or an unstated precondition): `Tx.Bucket`
  says a bucket instance "is only valid for the lifetime of the transaction", with no word on
  `DeleteBucket`; within the same transaction, a handle taken before its bucket is deleted (and
  re-created) panics on `Put`, or reads and deletes as if the bucket were empty, returning no
  error. Reproduced at v1.5.0. Not reachable through etcd: its backend looks the bucket up by
  name for every operation.
- **Where**: bbolt v1.5.0.
  - `tx.go:108-110` (`Tx.Bucket`): "The bucket instance is only valid for the lifetime of the
    transaction."; `tx.go:129-130`, `bucket.go:271-272` (`DeleteBucket`) say nothing about
    handles.
  - `bucket.go:273-...` (`Bucket.DeleteBucket`): removes the cached child from `b.buckets` and
    sets the child's `nodes` and `rootNode` to nil, then frees its pages; the old `*Bucket`
    stays usable as far as its API says (`Put`'s checks, `bucket.go:452-472`, are on the
    transaction only).
  - etcd: `server/storage/backend/batch_tx.go:170,195,230` and `read_tx.go:103` call
    `tx.Bucket(name)` for each operation, so no handle outlives a `DeleteBucket`.
- **What happens**: `repro_test.go` (copy into bbolt's package directory, `go test -run
  TestReproDeletedBucket`):
  - `TestReproDeletedBucketHandlePutPanics`: `CreateBucketIfNotExists("a")` (handle `old`),
    `DeleteBucket("a")`, `CreateBucketIfNotExists("a")`, then `old.Put` panics: `assertion
    failed: nodes map expected`.
  - `TestReproDeletedBucketHandleSilent`: the same with a key put through `old` before the
    delete and `k2` put through the new handle after it: `old.Delete("k2")` returns nil and
    leaves `k2`, and `old.Cursor().Seek("k2")` returns nil though bucket `a` holds `k2`.
- **Expected**: either the documentation says a handle is invalid once its bucket (or an
  ancestor) is deleted, or the handle's operations return an error (e.g. `ErrBucketNotFound`)
  instead of panicking or acting on the freed bucket.
- **How the proof handles it**: bbolt's trust-boundary specs give a handle at its bucket's
  generation (`wBkt tx b n g`) and `Tx.DeleteBucket_kv` bumps the name's generation, so `Put`,
  `Delete` and `Cursor` through a deleted bucket's handle are not allowed (`G n = g`,
  `Spec/go_etcd_io/bbolt/Bucket__Put_kv.lean`; since 2026-10-27, `notes/decisions.md`, "bbolt
  handles at a generation"). Until then `wBkt tx b n` was persistent across the delete: the
  audit's latent false row (`notes/audit.md`, "bbolt", the `wBkt` trio). No proof reached the
  failing instance (the backend re-fetches handles).
- **Possible fixes**: document it on `Tx.Bucket`/`DeleteBucket`; or mark the deleted child (and
  its descendants) so that their methods return `ErrBucketNotFound`.
- **Found**: 2026-10-27, by `etc/spec-test/bbolt` (step 2 of `notes/spec-first-plan.md`): a
  spec-guided random call sequence over the current bbolt specs, which reached the persistent
  `wBkt` of a deleted bucket in 26 of 3000 runs (panic) and 2 more (silent wrong result).
