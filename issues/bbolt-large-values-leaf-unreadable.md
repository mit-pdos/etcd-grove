---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/bbolt#931 issue closed: huge values panicking after a refactor shrank MaxAllocSize (fixed by #968); one value, a different cause
  - etcd-io/bbolt#182 issue closed: a slice-bounds panic in leafPageElement.key with small values (corruption); not this
blocks-proof: no
---

# bbolt: `Get` panics on values committed together whose sizes add up to more than 2 GiB

Values that `Put` accepts and `Commit` stores cannot be read back when they share a leaf page
larger than 2 GiB: a write transaction puts two values of 1 GiB − 1 under the keys `a` and `b` and
commits without error, and `Get("b")` then panics. A bucket of at most four keys always has all
its values on one page, since bbolt never splits a leaf that small.

**Expected:** `Get` should return each value a committed transaction stored; every value is within
[`MaxValueSize`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L16-L17)
and `Commit` returned nil.

**Impact:** applications storing several values of hundreds of MiB or more in one bucket, on
64-bit platforms (on 32-bit ones `MaxAllocSize` is 256 MB, so far smaller values). The data is
committed and unreadable: cursors and `Tx.Check` read through the same accessor. Not etcd, whose
request size limit (1.5 MiB by default) keeps entries tiny. Present in v1.5.0 and on `main`.

**Reproduction:** `TestDB_HugeValues` in
[`issues/bbolt-large-values-leaf-unreadable/huge_values_test.go`](bbolt-large-values-leaf-unreadable/huge_values_test.go),
copied into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 (2026-10-16),
go1.27.3 linux/amd64 (about 5 GB of memory):

```
$ go test . -run 'TestDB_HugeValues$' -count=1 -v
=== RUN   TestDB_HugeValues
--- FAIL: TestDB_HugeValues (15.24s)
panic: runtime error: slice bounds out of range [::2147483664] with length 2147483647 [recovered, repanicked]
go.etcd.io/bbolt/internal/common.(*leafPageElement).Value(...)
	internal/common/page.go:320
go.etcd.io/bbolt.(*Cursor).keyValue(...)
go.etcd.io/bbolt.(*Cursor).seek(...)
go.etcd.io/bbolt.(*Bucket).Get(...)
go.etcd.io/bbolt_test.TestDB_HugeValues.func3(...)
	huge_values_test.go:47
```

**Cause:** [`splitTwo`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/node.go#L229-L234)
never splits a node of at most four inodes, and
[`splitIndex`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/node.go#L271-L291)
always puts at least two inodes on a page, however large they are.
[`leafPageElement.Value`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/page.go#L317-L321)
slices from the element's address through a `[MaxAllocSize]byte` array, so on a page larger than
`MaxAllocSize` the later values cannot be read. Past 4 GiB from an element the `uint32` positions
would also wrap (not reproduced: the read panics first).

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the bbolt proof's spill (branch `bbolt`, in progress: `SpillFit.lean`) assumes each entry's
key plus value is at most `2^28` bytes and the page size below 1 MiB, so that a written page's
elements stay inside `MaxAllocSize`; `Put`'s documented bounds do not give it; etcd meets it.

## Fix

**Branch**: `fix/bbolt-large-values-leaf-unreadable` in `~/etcd-fixes/bbolt-large-values-leaf-unreadable` (upamanyus/bbolt, not pushed): e8f9d2b test, b71c0a2 fix
**Base**: etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8

**PR draft**:

Title: node: split a node too large to be read back from one page

[`splitTwo`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/node.go#L229-L234) never splits a node of at most four inodes, and [`splitIndex`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/node.go#L271-L291) always puts at least two inodes on a page, however large they are. [`leafPageElement.Value`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/page.go#L317-L321) slices from the element's address through a `[MaxAllocSize]byte` array, so on a page larger than `MaxAllocSize` the later values cannot be read. This PR also splits a node that would be larger than `MaxAllocSize`, down to one inode per page if needed.

The first commit adds a test of how the issue's example is split into pages, which fails on `main`; the second, the fix, makes it pass.

The branch's test is `TestNode_split_MaxAllocSize` (the node of the issue's two values must split
into pages of at most `MaxAllocSize`; no memory, fails on `main` with `exp<=2147483647;
got=2147483710`), not the end-to-end `TestDB_HugeValues`: that one needs 5 GB at the base, 9 GB
with the fix and 23 GB under `-race`, more than bbolt's 16 GB CI runners. Alternatives: slice from
the data start in the accessors (leaves the `uint32` wrap); lower `MaxValueSize` to a quarter of
`MaxAllocSize` (rejects values that work today). Complements `bbolt-max-value-size-unusable`
(a single entry too large for any page cannot be split; merge clean).
