---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/bbolt#931 issue closed: the same panic for values above 256 MB (a refactor had shrunk MaxAllocSize); fixed in v1.4.1
  - etcd-io/bbolt#968 pr merged: the fix of #931 (MaxAllocSize platform-dependent again); this is the edge that remains at that bound
---

# Values near `MaxValueSize` panic `Commit`, or commit and then panic every read

- **Status**: a bug: values `Put` accepts make the transaction panic or the bucket unreadable;
  both reproduced by Go tests at v1.5.0 (amd64).
- **Where**: bbolt v1.5.0 (upstream `main` unchanged as of 2026-10-19).
  - `bucket.go:17`: `MaxValueSize = (1 << 31) - 2`; `bucket.go:469-472` (`Put`) checks the key
    against `MaxKeySize` and the value against `MaxValueSize`, separately.
  - `internal/common/unsafe.go:26`: `UnsafeByteSlice` slices `(*[MaxAllocSize]byte)(base+off)[i:j:j]`;
    `MaxAllocSize = 0x7FFFFFFF` on 64-bit (`bolt_amd64.go:7`).
  - `internal/common/inode.go:81` (`WriteInodeToPage`): `UnsafeByteSlice(p, off, 0, len(key)+len(value))`.
  - `internal/common/page.go:310-321` (`leafPageElement.Key`/`Value`): `UnsafeByteSlice(elem, 0, pos, pos+size)`.
  - `node.go:232` (`splitTwo`): a node of at most `2 * MinKeysPerPage` = 4 inodes is never split.
- **What happens**:
  1. **One value**: `Put(key, value)` with `len(value) = MaxValueSize` and `len(key) ≥ 2`
     passes both checks; `Commit`'s `node.write` slices `len(key)+len(value) ≥ 2^31` bytes out of
     a `[MaxAllocSize]byte` array: `panic: runtime error: slice bounds out of range
     [::2147483648] with length 2147483647` (`TestReproMaxValueSizePanics`).
  2. **Several values in one leaf**: a leaf of at most four entries is not split however large,
     so three values of `MaxValueSize - 16` bytes commit into one page of about 6 GiB. Each
     element's accessor slices from the element's address through a `[MaxAllocSize]byte` array,
     and the second value's data starts more than `2^31` bytes after its element: every read of
     that leaf panics, `Get` and any cursor search through it (`panic: runtime error: slice
     bounds out of range [::2147483664] with length 2147483647` in `Cursor.nsearch`,
     `TestReproLeafPosWraps`). The data is committed and unreadable; past 4 GiB the elements'
     `uint32` positions (`inode.go:87`) would wrap as well.

  Reproduction: [`bbolt-max-value-size-unusable/repro_test.go`](bbolt-max-value-size-unusable/repro_test.go)
  (copy into bbolt's package directory; `BBOLT_REPRO_BIG=1 go test -run 'TestReproMaxValueSize|TestReproLeafPos'`;
  about 6 and 20 GiB of memory).
- **Expected**: a value `Put` accepts can be committed and read back; or `Put` rejects it
  (`ErrValueTooLarge`).
- **How the proof handles it**: the bbolt proof's spill (branch `bbolt`; in progress, not yet
  committed: `SpillFit.lean`) assumes each entry's key plus value is at most `2^28` bytes and the page size below 1 MiB, so that a
  written page's elements stay inside `MaxAllocSize`.
- **Possible fixes**: bound `len(key) + len(value)` in `Put` (by `MaxAllocSize` minus the page
  header and element), and split a leaf whose data exceeds `MaxAllocSize` regardless of its
  number of inodes (or lower `MaxValueSize` so that four of them fit, and check it).
- **Found**: 2026-10-13/18, the bbolt proof (`node.write`, the spill's page bounds); reproduced
  2026-10-19.
