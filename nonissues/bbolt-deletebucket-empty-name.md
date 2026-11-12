---
upstream: none
checked: 2026-11-12
links: []
blocks-proof: no
---

# bbolt: `DeleteBucket` of the empty name reports an incompatible value when the bucket's first leaf is empty

In a write transaction whose root bucket has no bucket, `tx.DeleteBucket([]byte{})` returns
`ErrIncompatibleValue`; once the root holds a bucket it returns `ErrBucketNotFound`, except when
this transaction's deletes emptied the root's first leaf: then it returns `ErrIncompatibleValue`
again, although buckets remain (2000 buckets, the first 50 deleted). No bucket can
be named by the empty name (`CreateBucket` refuses it with `ErrBucketNameRequired`), so the expected
answer is `ErrBucketNotFound` either way.

**Why not an issue:** a wrong error value only, on a name no bucket can have; etcd's backend never
deletes a bucket by the empty name. Cause: the cursor's `seek` of `""` in an empty root bucket
returns a nil key, and `bytes.Equal([]byte{}, nil)` is true, so `DeleteBucket` takes the nil
entry (flags `0`) for a found key that is not a bucket (`bucket.go:296-305`). The seek descends to
the first leaf (index 0), and a leaf node emptied by the transaction's deletes also gives a nil key
(`cursor.go`'s `keyValue` at `count() == 0`), so the same happens in a non-empty bucket.

## Proof

no: the frozen `Tx.DeleteBucket.spec` allows, for the empty name, `ErrIncompatibleValue` with the
transaction unchanged besides `ErrBucketNotFound` (`Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean`,
D-M in `notes/bbolt-spec-decisions.md`, decided by the coordinator, for the user's review). The spec
plan's `Tx.DeleteBucket.spec`/`Bucket.DeleteBucket.spec` had made the arm exact (`ErrIncompatibleValue`
only in an empty bucket), false in the emptied-leaf case; they allow either error again
(`notes/specs-only/ledger.md`, 2026-11-12).

## Notes

Test: [`bbolt-deletebucket-empty-name/empty_name_test.go`](bbolt-deletebucket-empty-name/empty_name_test.go)
(package `bbolt_test`), at upamanyus/bbolt@743299d (the goosed fork), go1.27: it logs
`empty root: incompatible value (notfound=false incompatible=true)` and `nonempty root: bucket
not found`. Found by U7m (2026-11-05) proving `Tx.DeleteBucket`.
[`emptied_leaf_test.go`](bbolt-deletebucket-empty-name/emptied_leaf_test.go), same commit and package
(2026-11-12, the spec plan's bbolt review): it logs `first remaining "bucket-000050";
DeleteBucket("") = incompatible value`.
