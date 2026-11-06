---
upstream: none
checked: 2026-11-05
links: []
blocks-proof: no
---

# bbolt: `DeleteBucket` of the empty name reports an incompatible value in an empty database

In a write transaction whose root bucket has no bucket, `tx.DeleteBucket([]byte{})` returns
`ErrIncompatibleValue`; once the root holds a bucket it returns `ErrBucketNotFound`. No bucket can
be named by the empty name (`CreateBucket` refuses it with `ErrBucketNameRequired`), so the expected
answer is `ErrBucketNotFound` either way.

**Why not an issue:** a wrong error value only, on a name no bucket can have; etcd's backend never
deletes a bucket by the empty name. Cause: the cursor's `seek` of `""` in an empty root bucket
returns a nil key, and `bytes.Equal([]byte{}, nil)` is true, so `DeleteBucket` takes the nil
entry (flags `0`) for a found key that is not a bucket.

## Proof

no: the frozen `Tx.DeleteBucket.spec` allows, for the empty name, `ErrIncompatibleValue` with the
transaction unchanged besides `ErrBucketNotFound` (`Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean`,
D-M in `notes/bbolt-spec-decisions.md`, decided by the coordinator, for the user's review).

## Notes

Test: [`bbolt-deletebucket-empty-name/empty_name_test.go`](bbolt-deletebucket-empty-name/empty_name_test.go)
(package `bbolt_test`), at upamanyus/bbolt@743299d (the goosed fork), go1.27: it logs
`empty root: incompatible value (notfound=false incompatible=true)` and `nonempty root: bucket
not found`. Found by U7m (2026-11-05) proving `Tx.DeleteBucket`.
