---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/bbolt#931 issue closed: the same panic for values above 256 MB (a refactor had shrunk MaxAllocSize); fixed in v1.4.1
  - etcd-io/bbolt#968 pr merged: the fix of #931 (MaxAllocSize platform-dependent again); this is the edge that remains at that bound
  - etcd-io/bbolt#1044 issue closed: the same Commit panic on i386 (a 256 MB value, the 32-bit MaxAllocSize); the maintainer called it expected and fixed only the test (#1045)
blocks-proof: yes
---

# bbolt: `Put` accepts a value of `MaxValueSize` bytes that `Commit` or `Get` then panics on

`Bucket.Put` accepts a value of `MaxValueSize` bytes, but the entry cannot be stored: with a
2-byte key the transaction's `Commit` panics; with a 1-byte key `Put` and `Commit` succeed and
every later `Get` of the key (and `Tx.Check`) panics. The same happens for any key and value whose
lengths add up to more than 2147483631 bytes (2 GiB − 17), even when each is within `MaxKeySize`
and `MaxValueSize`.

**Expected:** `Put` should return `ErrValueTooLarge` for a key and value bbolt cannot store, as
it does for a value longer than
[`MaxValueSize`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L16-L17)
("the maximum length of a value, in bytes").

**Impact:** applications storing values near 2 GiB on 64-bit platforms (on 32-bit platforms the
bound is 256 MB, bbolt#1044). The second case leaves a committed entry no read can return. Not
etcd, whose request size limit (1.5 MiB by default) keeps values far below it. Present in v1.5.0
and on `main`.

**Reproduction:** `TestBucket_Put_MaxValueSizeWithKey` in
[`issues/bbolt-max-value-size-unusable/max_value_size_test.go`](bbolt-max-value-size-unusable/max_value_size_test.go),
copied into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 (2026-10-16),
go1.27.3 linux/amd64, one subtest at a time (about 2 GB of memory each):

```
$ go test . -run 'TestBucket_Put_MaxValueSizeWithKey/^ab$' -count=1 -v
--- FAIL: TestBucket_Put_MaxValueSizeWithKey (5.71s)
    --- FAIL: TestBucket_Put_MaxValueSizeWithKey/ab (5.71s)
panic: runtime error: slice bounds out of range [::2147483648] with length 2147483647 [recovered, repanicked]
go.etcd.io/bbolt/internal/common.WriteInodeToPage(...)
	internal/common/inode.go:81
go.etcd.io/bbolt.(*node).write(...)
$ go test . -run 'TestBucket_Put_MaxValueSizeWithKey/^a$' -count=1 -v
    max_value_size_test.go:28:
        	Error:      	Expected error with "value too large" in chain but got nil.
        	Test:       	TestBucket_Put_MaxValueSizeWithKey/a
consistency check failed (1 errors)
runtime error: slice bounds out of range [::2147483663] with length 2147483647
FAIL	go.etcd.io/bbolt	16.758s
```

**Cause:** [`Put`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L540-L546)
checks the key against `MaxKeySize` and the value against `MaxValueSize` separately, but a page
holding the entry must fit in `MaxAllocSize` (2 GiB − 1 on 64-bit platforms):
[`WriteInodeToPage`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/inode.go#L80-L81)
and [`leafPageElement.Value`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/page.go#L317-L321)
slice the entry out of a `[MaxAllocSize]byte` array, the latter from the element header, 16
bytes before the key.

## Proof

yes: the bbolt proof's spill (branch `bbolt`, in progress: `SpillFit.lean`) assumes each entry's
key plus value is at most `2^28` bytes, which `Put`'s documented bounds do not give; etcd meets
it.

## Fix

**Branch**: `fix/bbolt-max-value-size-unusable` in `~/etcd-fixes/bbolt-max-value-size-unusable` (upamanyus/bbolt, not pushed): 1283e4e test, 668f5c0 fix
**Base**: etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8

**PR draft**:

Title: bucket: reject a value too large to be stored with its key

[`Put`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/bucket.go#L540-L546) checks the key against `MaxKeySize` and the value against `MaxValueSize` separately, but a page holding the entry must fit in `MaxAllocSize` (2 GiB − 1 on 64-bit platforms): [`WriteInodeToPage`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/inode.go#L80-L81) and [`leafPageElement.Value`](https://github.com/etcd-io/bbolt/blob/a4ef19710eb7ddc41fd1155336baf331b5c57ba8/internal/common/page.go#L317-L321) slice the entry out of a `[MaxAllocSize]byte` array. This PR makes `Put` return `ErrValueTooLarge` when a page holding only the key and value would be larger than `MaxAllocSize`.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

The fix's bound is 16 bytes tighter than the exact limit for an entry alone on a page
(`len(key)+len(value) <= MaxAllocSize-16`), so a value of `MaxValueSize-16` with a 1-byte key,
readable today, is now refused. Alternatives: lower `MaxValueSize` (an exported constant), or
raise `MaxAllocSize` on 64-bit (the `uint32` element fields keep a limit). Independent of
`bbolt-large-values-leaf-unreadable`'s fix (different files, merge clean): with only that one, a
single oversized entry is still accepted.

## Notes

The fork `upamanyus/bbolt` now exists (it holds #1312's branch); push the branch before filing.
