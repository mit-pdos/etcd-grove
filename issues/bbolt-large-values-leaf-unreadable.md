---
upstream: none
checked: 2026-10-23
links:
  - etcd-io/bbolt#931 issue closed: huge values panicking after a refactor shrank MaxAllocSize (fixed by #968); one value, a different cause
  - etcd-io/bbolt#182 issue closed: a slice-bounds panic in leafPageElement.key with small values (corruption); not this
candidate: issues/upstream/bbolt-large-values-leaf-unreadable/
---

# Values committed together on one page larger than `MaxAllocSize` panic every read

- **Status**: a bug: values `Put` accepts and `Commit` stores cannot be read back (`Get` panics; cursors and
  `Tx.Check` read through the same accessor), reproduced by a Go test at upstream `main` a4ef197 (amd64). Split on 2026-10-23
  from [bbolt-max-value-size-unusable](bbolt-max-value-size-unusable.md) (one entry too large for
  any page: a different cause, trigger and fix).
- **Where**: bbolt v1.5.0 (upstream `main` unchanged as of 2026-10-23, a4ef197).
  - `node.go:229-234` (`splitTwo`): a node of at most `2 * MinKeysPerPage` = 4 inodes is never split.
  - `node.go:271-291` (`splitIndex`): a page gets at least `MinKeysPerPage` = 2 inodes, whatever their size.
  - `internal/common/page.go:310-321` (`leafPageElement.Key`/`Value`): `UnsafeByteSlice(elem, 0, pos,
    pos+size)` through a `[MaxAllocSize]byte` array (`MaxAllocSize = 0x7FFFFFFF` on 64-bit).
  - `internal/common/inode.go:87` (`WriteInodeToPage`): `pos` is a `uint32`.
- **What happens**: two values of `MaxAllocSize/2` bytes (1 GiB − 1) under the keys `a` and `b`
  commit into one leaf page of about 2 GiB (the node has two inodes, so it is not split); `b`'s
  element is 32 bytes into the page and its value ends more than `MaxAllocSize` bytes after the
  element, so `Get("b")` panics: `slice bounds out of range [::2147483664] with length 2147483647`
  (`Cursor.keyValue` → `leafPageElement.Value`). With more keys, `splitIndex` still pairs two large
  neighbours on one page. Past 4 GiB from an element (three or four values near 2 GiB, which a leaf of
  four keys allows) the `uint32` positions would also wrap; not reproduced (the read panics first).

  Reproduction: the issue's end-to-end test (`TestDB_HugeValues`, in
  `issues/upstream/bbolt-large-values-leaf-unreadable/issue.md`; about 5 GB of memory at the base, 9 GB
  with the fix, 23 GB under `-race`), and `TestReproLeafPosWraps` in
  [`bbolt-max-value-size-unusable/repro_test.go`](bbolt-max-value-size-unusable/repro_test.go) (three
  values of `MaxValueSize - 16`; it panics in `Cursor.nsearch` the same way). The candidate's branch
  test is the split itself (`TestNode_split_MaxAllocSize`, no memory).
- **Expected**: a value `Put` accepted and `Commit` stored can be read back.
- **How the proof handles it**: the bbolt proof's spill (branch `bbolt`; in progress, not yet
  committed: `SpillFit.lean`) assumes each entry's key plus value is at most `2^28` bytes and the page
  size below 1 MiB, so that a written page's elements stay inside `MaxAllocSize`.
- **Possible fixes**: split a node larger than `MaxAllocSize` even below the minimum number of keys,
  down to one inode per page (the candidate); slice from the data start in the accessors (leaves the
  `uint32` wrap); lower `MaxValueSize` to a quarter of `MaxAllocSize` (rejects values that work today).
  The candidate's `meta.md` compares them.
- **Found**: 2026-10-13/18, the bbolt proof (the spill's page bounds); reproduced 2026-10-19 (as part
  of bbolt-max-value-size-unusable) and 2026-10-23 (`TestDB_HugeValues`).
