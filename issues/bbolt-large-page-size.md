---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/bbolt#447 issue closed: "Remove panics in the library code", lists the inode-overflow panic, not its trigger
---

# A large `Options.PageSize` is accepted, then panics or is stored truncated

- **Status**: an unstated precondition (`Options.PageSize` has no upper bound) whose violations
  panic; two of three cases reproduced by Go tests at v1.5.0, the third by code reading.
  Needs a non-default page size of at least about 1 MiB; etcd uses the default.
- **Where**: bbolt v1.5.0 (upstream `main` unchanged as of 2026-10-19).
  - `db.go:262`: `db.pageSize = options.PageSize`, not checked; `db.go:1369-1370` documents the
    option ("overrides the default OS page size") with no bound.
  - `tx.go:582` (`Tx.write`): single pages go back to the pool as
    `common.UnsafeByteSlice(p, 0, 0, tx.db.pageSize)`, a slice of a `[MaxAllocSize]byte` array.
  - `node.go:189-191` (`node.write`): `panic("inode overflow")` for 65535 inodes or more (a
    page's count is a `uint16`); `node.go:232` (`splitTwo`) does not split a node that fits one page.
  - `db.go:658` (`init`): `m.SetPageSize(uint32(db.pageSize))`.
- **What happens**:
  1. `PageSize: 1 << 31` (above `MaxAllocSize = 2^31 - 1`): `Open` creates the database; the
     first `Commit` panics in `Tx.write` (`slice bounds out of range [::2147483648] with length
     2147483647`; `TestReproPageSizeAboveMaxAlloc`, about 20 GiB of memory, an 8 GiB file).
  2. `PageSize: 8 << 20`: 70000 small entries in one bucket fit one page, so they are not split,
     and `Commit` panics (`inode overflow: 70000`; `TestReproLargePageInodeOverflow`). A page of
     about 1 MiB or more holds 65535 minimal entries (here the bucket was still inline:
     `Bucket.write`; a larger bucket reaches the same check through `node.spill`).
  3. `PageSize` of `2^32` or more: the meta records `uint32(pageSize)`, so a reopened database
     reads another page size (code reading; not run: the file would be 16 GiB).

  Reproduction: [`bbolt-large-page-size/repro_test.go`](bbolt-large-page-size/repro_test.go)
  (copy into bbolt's package directory; `go test -run TestReproLargePageInodeOverflow`, and
  `BBOLT_REPRO_BIG=1 go test -run TestReproPageSizeAboveMaxAlloc`).
- **Expected**: `Open` rejects a page size bbolt cannot use (`ErrInvalid`, or a documented bound).
- **How the proof handles it**: the bbolt proof (branch `bbolt`) takes `pageSize < 2^31` as a
  premise of `Tx.write` (`Spec/go_etcd_io/bbolt/Tx__write.lean`), `< 2^32` of `init`/`Open`, and
  below 1 MiB for the spill (in progress: `SpillFit.lean`).
- **Possible fixes**: validate `Options.PageSize` in `Open` (e.g. a power of two between 1 KiB
  and 1 MiB, or at most `MaxAllocSize` with `node.write` splitting by count as well as size), and
  document the bound.
- **Found**: 2026-10-12/18, the bbolt proof (`init`'s page size bound, `node.write`, `Tx.write`, the
  spill);
  reproduced 2026-10-19.
