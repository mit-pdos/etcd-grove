---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/bbolt#931 issue closed: the same panic for values above 256 MB (a refactor had shrunk MaxAllocSize); fixed in v1.4.1
  - etcd-io/bbolt#968 pr merged: the fix of #931 (MaxAllocSize platform-dependent again); this is the edge that remains at that bound
  - etcd-io/bbolt#1044 issue closed: the same Commit panic on i386 (a 256 MB value, the 32-bit MaxAllocSize); the maintainer called it expected and fixed only the test (#1045)
candidate: issues/upstream/bbolt-max-value-size-unusable/
---

# A value of `MaxValueSize` bytes panics `Commit`, or commits and then panics every read

- **Status**: a bug: a key and value `Put` accepts make the transaction panic, or commit an entry
  that no read can return; both reproduced by Go tests at v1.5.0 and at upstream `main` a4ef197
  (amd64). The finding first also covered several large values on one page, a distinct cause and
  fix: split out to [bbolt-large-values-leaf-unreadable](bbolt-large-values-leaf-unreadable.md)
  (2026-10-23).
- **Where**: bbolt v1.5.0 (upstream `main` unchanged as of 2026-10-23, a4ef197).
  - `bucket.go:17`: `MaxValueSize = (1 << 31) - 2`; `bucket.go:540-546` (`Put`) checks the key
    against `MaxKeySize` and the value against `MaxValueSize`, separately.
  - `internal/common/unsafe.go:26`: `UnsafeByteSlice` slices `(*[MaxAllocSize]byte)(base+off)[i:j:j]`;
    `MaxAllocSize = 0x7FFFFFFF` on 64-bit (`bolt_amd64.go:7`).
  - `internal/common/inode.go:80-81` (`WriteInodeToPage`): `UnsafeByteSlice(p, off, 0, len(key)+len(value))`.
  - `internal/common/page.go:310-321` (`leafPageElement.Key`/`Value`): `UnsafeByteSlice(elem, 0, pos, pos+size)`.
- **What happens**: a page holding one entry is the page header (16 bytes), one element (16), the
  key and the value.
  1. `len(key)+len(value) > MaxAllocSize` (`Put(key, value)` with `len(value) = MaxValueSize` and
     `len(key) ≥ 2`): `Commit`'s `node.write` slices that many bytes out of a `[MaxAllocSize]byte`
     array: `panic: runtime error: slice bounds out of range [::2147483648] with length 2147483647`
     (`TestReproMaxValueSizePanics`).
  2. `MaxAllocSize-16 < len(key)+len(value) ≤ MaxAllocSize` (a 1-byte key): `Commit` succeeds, and
     `Get` (and `Tx.Check`) panic in `leafPageElement.Value`, which slices up to `pos+ksize+vsize` from
     the element (`pos` = 16): `[::2147483663] with length 2147483647`. The entry is committed and
     unreadable.

  Reproduction: [`bbolt-max-value-size-unusable/repro_test.go`](bbolt-max-value-size-unusable/repro_test.go)
  (`TestReproMaxValueSizePanics`; copy into bbolt's package directory, `BBOLT_REPRO_BIG=1 go test
  -run TestReproMaxValueSize`), and the candidate's test `TestBucket_Put_MaxValueSizeWithKey`
  (both cases).
- **Expected**: a key and value `Put` accepts can be committed and read back; or `Put` rejects
  them (`ErrValueTooLarge`).
- **How the proof handles it**: the bbolt proof's spill (branch `bbolt`; in progress, not yet
  committed: `SpillFit.lean`) assumes each entry's key plus value is at most `2^28` bytes and the page size below 1 MiB, so that a
  written page's elements stay inside `MaxAllocSize`.
- **Possible fixes**: bound `len(key) + len(value)` in `Put` by `MaxAllocSize` minus the page
  header and element (the candidate); or lower `MaxValueSize` (an exported constant); or raise
  `MaxAllocSize` on 64-bit (the `uint32` element fields keep a limit). The candidate's `meta.md`
  compares them.
- **Found**: 2026-10-13/18, the bbolt proof (`node.write`, the spill's page bounds); reproduced
  2026-10-19; split 2026-10-23.
