---
upstream: known
checked: 2026-11-03
links:
  - etcd-io/bbolt#1305 pr open: "bucket: do not skip child buckets in DeleteBucket", the same bug and its fix (collect the child keys first, then delete)
blocks-proof: no
---

# bbolt: `DeleteBucket` leaks a nested bucket's pages when the bucket was written in the same transaction

Deleting a bucket that holds nested buckets can skip one of them, so that its pages are never
freed. This happens when the bucket was written earlier in the same write transaction (a `Put` or
`CreateBucket` into it). After the commit, the skipped bucket's pages are neither reachable nor
free: the file never reuses that space, and `tx.Check()` (`bbolt check`) reports
`unreachable unfreed`. Without the earlier write, every nested bucket is freed.

**Expected:** `DeleteBucket` should release every page of the deleted bucket and of all its nested
buckets, as its comment says ("Recursively delete all child buckets … Release all bucket pages to
freelist",
[`bucket.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L333-L351)).

**Impact:** applications that nest buckets, then write into a bucket and delete it in one
transaction. The leaked pages stay allocated for the life of the file. The leak is persisted with
the synced freelist; with `NoFreelistSync`, a reopen rebuilds the freelist by scanning and
recovers them. No data is lost and nothing panics. etcd is not affected: its backend has no
nested buckets. Present in v1.5.0 and on `main`.

**Reproduction:** `TestDeleteBucketNestedLeak` in
[`issues/bbolt-deletebucket-nested-leak/deletebucket_nested_leak_test.go`](bbolt-deletebucket-nested-leak/deletebucket_nested_leak_test.go),
copied into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 (2026-10-16),
go1.27.3 linux/amd64:

```
$ go test . -run TestDeleteBucketNestedLeak -count=1 -v
=== RUN   TestDeleteBucketNestedLeak
    deletebucket_nested_leak_test.go:57: check: page 17: unreachable unfreed
    deletebucket_nested_leak_test.go:57: check: page 18: unreachable unfreed
    ...
    deletebucket_nested_leak_test.go:57: check: page 29: unreachable unfreed
--- FAIL: TestDeleteBucketNestedLeak (0.00s)
FAIL
```

That is 13 pages, one nested bucket's. The setup commits a bucket `A` with three nested buckets of
200 entries each. A second transaction does `A.Put("z", "v")` and then `tx.DeleteBucket("A")`.
- Without the `Put`, the test passes.
- It fails the same way on the goose fork (`upamanyus/bbolt` `b3e06648`, v1.5.0 plus the
  verification fixes).

**Cause:**
- `DeleteBucket` deletes the nested buckets from inside `child.ForEachBucket`'s callback
  ([`bucket.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L335-L340)).
  `ForEach`'s documentation says that callback must not modify the bucket.
- When the bucket's leaf is already in memory (a node, because of the earlier write), the inner
  `DeleteBucket` removes its entry from that node
  ([`bucket.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L354)).
  The following entries shift down by one.
- The outer cursor's `next`
  ([`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L215))
  then moves to the next index, skipping the entry after the deleted one.
- A skipped nested bucket is never deleted. `child.free()` frees only the deleted bucket's own
  pages
  ([`bucket.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L351)),
  so its pages leak.

## Proof

no: the bbolt specs cover top-level buckets only (`fileHolds` admits no nested bucket, and no
specified operation creates one), so `DeleteBucket`'s recursion never runs in the proof. A leaked
page would also be one of the invariant's leaked W slots (`bbolt-inv/design.md`, B2). Found by the
third review of the bbolt invariant design (`review-3.md`, N8).

## Fix

**Branch**: none; etcd-io/bbolt#1305 (open) has the fix (collect the nested buckets' keys, then
delete them) and a regression test.

## Notes

Upstream search (2026-11-03, `gh search`): no issue; PR #1305 covers it.

Re-run 2026-11-03 at etcd-io/bbolt@a4ef19710eb7 (an archive of the commit, the test copied into
its root, go1.27.3 linux/amd64): fails as above, pages 17 to 29 `unreachable unfreed` (13 pages),
`--- FAIL: TestDeleteBucketNestedLeak`.
