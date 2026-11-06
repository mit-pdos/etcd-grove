---
upstream: none
checked: 2026-11-03
links: []
blocks-proof: no
---

# bbolt: `CreateBucket` accepts bucket names longer than `MaxKeySize`, though documented to refuse them

`Tx.CreateBucket`, `Tx.CreateBucketIfNotExists` (and `Bucket.CreateBucket`/`CreateBucketIfNotExists`)
are documented to return "an error ... if the bucket name is too long", but they check only that
the name is not empty: a name of `MaxKeySize + 1` bytes, or of 1 MiB, is accepted, committed and
read back. `Put` does check its key against `MaxKeySize` (`ErrKeyTooLarge`).

**Why not an issue:** documentation only, and a length etcd never uses: etcd's bucket names are a
few bytes (`server/storage/schema/bucket.go`). Either the documentation should drop "too long" or
the functions should return `ErrKeyTooLarge` (or a bucket-specific error) above `MaxKeySize`. A
name large enough to make the root's leaf page exceed `MaxAllocSize` would hit the same panic as
`issues/bbolt-max-value-size-unusable.md`.

## Proof

no: bbolt's API spec (2026-11-03, `Tx.CreateBucket`, `Tx.CreateBucketIfNotExists`) keeps
the premise `n.length ≤ maxKeySize`, as the trust-boundary `Tx.CreateBucketIfNotExists_kv` did: a
scope restriction stricter than the code (which checks nothing) but within the documented API;
etcd meets it.

## Notes

Test: `TestLongBucketName` in
[`nonissues/bbolt-bucket-name-length-unchecked/long_bucket_name_test.go`](bbolt-bucket-name-length-unchecked/long_bucket_name_test.go)
(package `bbolt_test`), copied into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8
(2026-10-16), go1.27.3 linux/amd64 (it fails the same way on v1.5.0):

```
$ go test . -run TestLongBucketName -count=1 -v
=== RUN   TestLongBucketName
    long_bucket_name_test.go:26: CreateBucket accepted a 32769-byte name (MaxKeySize 32768)
    long_bucket_name_test.go:33: CreateBucketIfNotExists accepted a 32770-byte name (MaxKeySize 32768)
    long_bucket_name_test.go:26: CreateBucket accepted a 1048576-byte name (MaxKeySize 32768)
    long_bucket_name_test.go:33: CreateBucketIfNotExists accepted a 1048577-byte name (MaxKeySize 32768)
--- FAIL: TestLongBucketName (0.08s)
```

The code there: `bucket.go`, the doc comments at lines 175 and 232, no length check in either
function. Upstream not searched
beyond that. Found 2026-11-03 while specifying the bucket API.
