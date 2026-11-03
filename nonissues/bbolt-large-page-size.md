---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/bbolt#447 issue closed: "Remove panics in the library code", lists the inode-overflow panic, not its trigger
blocks-proof: no
---

# bbolt: a large `Options.PageSize` is accepted, then panics or is stored truncated

`Open` does not bound `Options.PageSize`: from about 1 MiB a leaf of 65535 small entries fits one
page, is not split, and `Commit` panics (`inode overflow`); from `2^31` the first `Commit` panics in
`Tx.write` (a slice past `MaxAllocSize`); from `2^32` the meta stores `uint32(pageSize)`, so a
reopened database reads another page size (code reading).

**Why not an issue:** a precondition etcd meets, on an option nobody sets that large: etcd uses the
default (OS) page size; a page size of a mebibyte or more is not a configuration bbolt's users run.
A bound checked in `Open` (`ErrInvalid`) would be a cheap hardening.

## Proof

no: the bbolt proof (branch `bbolt`) takes the page size below `2^31` as a premise of `Tx.write`,
below `2^32` of `init`/`Open`, and below 1 MiB for the spill (in progress, `SpillFit.lean`); etcd's
default page size meets them.

## Notes

Tests: [`bbolt-large-page-size/repro_test.go`](bbolt-large-page-size/repro_test.go) (package
`bbolt`). `TestReproLargePageInodeOverflow` (`PageSize: 8 << 20`, 70000 entries) panics at
etcd-io/bbolt@a4ef197 (go1.27.3, 2026-11-01): `panic: inode overflow: 70000 (pgid=0)` from
`Bucket.write` in `Commit`. `TestReproPageSizeAboveMaxAlloc` (`BBOLT_REPRO_BIG=1`, about 20 GiB of
memory) panicked in `Tx.write` on 2026-10-19 at v1.5.0; not rerun.
