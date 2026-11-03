---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/bbolt#939 issue open: proposes removing the MADV_RANDOM hint (page faults on Linux 6.4+), which would remove this path
blocks-proof: no
---

# bbolt: a failed `madvise` leaks the new memory mapping

In `mmap` (`bolt_unix.go`), if `unix.Madvise(b, MADV_RANDOM)` fails (other than `ENOSYS`) the
function returns the error before `db.dataref = b`, so `munmap` never unmaps `b`. On a remap the old
mapping is already gone, so the database is also left without one (`ErrInvalidMapping` on the
next `Begin`).

**Why not an issue:** no test, found by code reading; `madvise` with `MADV_RANDOM` on a mapping
just made practically never fails, so no caller can reach the path on demand. A test could
promote it only with an injected `madvise` failure.

## Proof

no: the bbolt proof's file model (branch `bbolt`, `Proof/os/FileModel.lean`) lets `File.Close`
take a file whatever its mapping, and `DB.mmap`'s spec gives the leaked mapping to nobody; no
premise.

## Notes

The fix is one line (`unix.Munmap(b)` before returning, or ignore the hint's failure); removing
the hint (etcd-io/bbolt#940, proposed in #939) removes the path. Found 2026-10-12 by the bbolt
proof.
