---
upstream: none
checked: 2026-11-03
links:
  - etcd-io/bbolt#734 pr merged: "Stabilize the behaviour of Prev when the cursor already points to the first element" (bbolt#733), a different case of Prev (at the first element)
  - boltdb/bolt#450 issue closed: the same empty-page fault for Next/First, fixed there by skipping empty pages; Prev was not fixed
blocks-proof: no
---

# bbolt: `Cursor.Prev` returns nil in the middle of a bucket after deletes in the same transaction

In a write transaction that deleted enough keys to empty a leaf page, `Cursor.Prev` returns a nil
key and value when it reaches the emptied page, as if the cursor were at the start of the bucket,
although earlier keys exist. A backward iteration (`for k, _ := c.Last(); k != nil; k, _ =
c.Prev()`) stops early and misses every key before the emptied page. A fresh cursor, made after
the deletes as the `Cursor` documentation asks, shows it. Forward iteration, `First`, `Last` and
`Seek` are not affected.

**Expected:** `Prev` should move to the previous key in the bucket and return nil only at the
beginning, as its documentation says ("If the cursor is at the beginning of the bucket then a nil
key and value are returned",
[`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L104-L106)).

**Impact:** applications that delete keys and then iterate backward within the same write
transaction (for example, a "delete then scan for the previous key" pattern, or reverse iteration
inside `Update`). A deleted range must cover a whole leaf page, which happens for any deletion of
more than a page's worth of consecutive keys. Read transactions and later transactions are not
affected, because `Commit` rebalances and removes empty pages. etcd is not affected, since its
backend never calls `Prev`. Present in v1.5.0 and on `main`.

**Reproduction:** `TestPrevOverEmptyLeaf` in
[`issues/bbolt-cursor-prev-empty-leaf/prev_empty_leaf_test.go`](bbolt-cursor-prev-empty-leaf/prev_empty_leaf_test.go),
copied into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 (2026-10-16),
go1.27.3 linux/amd64:

```
$ go test . -run TestPrevOverEmptyLeaf -count=1 -v
=== RUN   TestPrevOverEmptyLeaf
    prev_empty_leaf_test.go:53: Prev after Seek(k01500): "" (expected "k00499")
    prev_empty_leaf_test.go:55: Prev returned "", want "k00499"
    prev_empty_leaf_test.go:62: backward walk saw 500 keys, want 1000
    prev_empty_leaf_test.go:64: backward walk saw 500 keys
    prev_empty_leaf_test.go:71: Last after deleting the tail: "k00499", want "k00499"
--- FAIL: TestPrevOverEmptyLeaf (0.02s)
FAIL
```

The setup commits 2000 keys, then in one write transaction deletes keys 500..1499, makes a new
cursor, `Seek`s to `k01500` and calls `Prev`.

**Cause:**
- `node.del` can leave a leaf node with no entries. Such nodes are removed only by `Commit`'s
  rebalance
  ([`tx.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/tx.go#L195)).
- `Cursor.prev`
  ([`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L251-L279))
  moves to the previous subtree and descends to its last leaf. When that leaf is empty, its index
  becomes `count() - 1 = -1`, and `keyValue` returns nil
  ([`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L374)).
- `next` skips empty pages
  ([`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L241),
  boltdb/bolt#450), and so does `Last`
  ([`cursor.go`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/cursor.go#L77)).
  `prev` does not. The fix is a loop in `Prev` that calls `prev` again while the current leaf is
  empty and the stack is not at the beginning.

## Proof

no: bbolt's API spec restricts `Cursor.Prev.spec` (`Spec/go_etcd_io/bbolt/Cursor__Prev.lean`) to
read transactions (`⌜T.rw = false⌝`, a scope restriction). A committed tree has no empty non-root
page (`fileHolds`'s well-formedness, kept by every commit's rebalance). etcd never calls `Prev`.
Found in a review of bbolt's API spec (2026-11-03, `notes/bbolt-spec-decisions.md`).
