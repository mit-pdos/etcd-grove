---
upstream: none
checked: 2026-11-03
links:
  - etcd-io/bbolt#734 pr merged: Prev at the first element stays there (bbolt#733); this is the loop that change closes in Last
  - boltdb/bolt#450 issue closed: empty pages after deletes in a write transaction, fixed for Next/First by skipping them
blocks-proof: no
---

# bbolt: `Cursor.Last` never returns after deleting every key of a bucket in the same transaction

In a write transaction that deleted every key of a bucket spanning several leaf pages,
`Cursor.Last()` loops forever instead of returning nil. A call that seeks the end of a bucket
just emptied (for example, to check whether anything is left) hangs the goroutine, and with it the
write lock of the database. `First`, `Seek` and `Next` return nil as expected.

**Expected:** `Last` should return a nil key and value for an empty bucket, as its documentation
says ("If the bucket is empty then a nil key and value are returned",
[`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L63-L66)).

**Impact:** applications that delete many keys of a bucket and then call `Last` on it within the
same write transaction, which is common for queues and logs trimmed from one end. The bucket must
have spanned more than one leaf page (a few kilobytes of data), and every leaf must be empty. The
writer then holds the database's write lock forever, so every later `Update` blocks. Read
transactions are not affected, because `Commit` rebalances and removes empty pages. etcd is not
affected, since its backend never calls `Last`. Present in v1.5.0 and on `main`.

**Reproduction:** `TestLastAllDeleted` in
[`issues/bbolt-cursor-last-empty-leaves-hang/last_all_deleted_test.go`](bbolt-cursor-last-empty-leaves-hang/last_all_deleted_test.go),
copied into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 (2026-10-16),
go1.27.3 linux/amd64:

```
$ go test . -run TestLastAllDeleted -count=1 -v
=== RUN   TestLastAllDeleted
    last_all_deleted_test.go:55: Last did not return within 5s (all leaves empty in a write tx)
--- FAIL: TestLastAllDeleted (5.04s)
FAIL
```

The setup commits 2000 keys of 100-byte values, then in one write transaction deletes them all and
calls `b.Cursor().Last()`.

**Cause:** `Last` skips empty leaves by calling `prev` while the current leaf is empty
([`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L76-L79)).
When every leaf is empty, `prev` climbs to the root and, since bbolt#734, calls `c.first()`
([`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L262-L266)).
That leaves the cursor on the first leaf, which is empty again, so the loop's condition never
becomes false. Empty leaves exist only in write transactions, between `node.del` and `Commit`'s
rebalance. A fix is to stop the loop when `prev` reports the beginning (or to have `Last` return
nil once the stack is back at the first leaf).

## Proof

no: a WP is partial, so bbolt's `Cursor.Last.spec` (`Spec/go_etcd_io/bbolt/Cursor__Last.lean`)
stays true: a call that never returns meets any post. Its docstring says the hang exists in
writers. etcd never calls `Last`. Found in a review of bbolt's API spec (2026-11-03,
`notes/bbolt-spec-decisions.md`).
