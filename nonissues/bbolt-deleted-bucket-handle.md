---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# bbolt: a bucket handle used after its bucket is deleted panics or silently misses the data

Within one write transaction, a `*Bucket` taken before `DeleteBucket` of its name (and the
bucket's re-creation) panics on `Put` (`assertion failed: nodes map expected`), and its `Delete`
and `Cursor().Seek` act on the freed bucket, returning no error and missing the new bucket's keys.
`Tx.Bucket` documents a handle as "only valid for the lifetime of the transaction" and says
nothing about deletion.

**Why not an issue:** a precondition etcd meets and documentation only: etcd's backend looks the
bucket up by name for every operation (`server/storage/backend/batch_tx.go`, `read_tx.go`), so no
handle outlives a `DeleteBucket`; using a handle to a deleted bucket is a use most bbolt users
would call a mistake, and the fix is a sentence on `Tx.Bucket`/`DeleteBucket` (or an
`ErrBucketNotFound` from the handle's methods).

## Proof

no: bbolt's trust-boundary specs give a handle at its bucket's generation (`wBkt tx b n g`), and
`Tx.DeleteBucket_kv` bumps the generation, so a deleted bucket's handle cannot be used
(`Spec/go_etcd_io/bbolt/Tx__DeleteBucket_kv.lean`, `Bucket__Put_kv.lean`; `notes/decisions.md`,
"bbolt handles at a generation"); etcd re-fetches handles.

## Notes

Tests: [`bbolt-deleted-bucket-handle/repro_test.go`](bbolt-deleted-bucket-handle/repro_test.go)
(package `bbolt`), both fail at etcd-io/bbolt@a4ef197 (go1.27.3, 2026-11-01):
`TestReproDeletedBucketHandlePutPanics`: `Put through the old handle panicked: assertion failed:
nodes map expected`; `TestReproDeletedBucketHandleSilent`: `bucket a holds k2, but the old
handle's cursor Seek(k2) returns "", and its Delete(k2) returned nil and left k2`. Found by the
spec tester `etc/spec-test/bbolt`, 2026-10-27. Before 2026-10-27 the specs let a handle survive
the delete (`notes/audit.md`, "bbolt", the `wBkt` trio).
