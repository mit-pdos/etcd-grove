---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/bbolt#939 issue open: proposes removing the MADV_RANDOM hint (page faults on Linux 6.4+), which would remove this path
---

# A failed `madvise` leaks the new memory mapping

- **Status**: a bug (a resource leak on an error path), minor: `madvise(MADV_RANDOM)` on a
  mapping just made practically never fails. From code reading, not reproduced.
- **Where**: bbolt v1.5.0 `bolt_unix.go:55-74` (`mmap`; upstream `main` unchanged as of
  2026-10-19): `unix.Mmap` returns `b`; if `unix.Madvise(b, MADV_RANDOM)` fails (other than
  `ENOSYS`) it returns the error before `db.dataref = b`; `munmap` (`bolt_unix.go:77-89`) unmaps
  only `db.dataref`.
- **What happens**: the mapping `b` is never unmapped: `DB.mmap` returns the error, and its
  callers' cleanup (`munmap`, `close`) sees no mapping. On a remap (`DB.allocate` growing the
  database) the old mapping was already unmapped, so the database is left without a mapping
  (`ErrInvalidMapping` on the next `Begin`) and the new one leaks.
- **Expected**: an error path that unmaps what it mapped.
- **How the proof handles it**: the bbolt proof's file model (branch `bbolt`,
  `Proof/os/FileModel.lean`) lets `File.Close` take a file whatever its mapping, since on Linux a
  mapping outlives its file; `DB.mmap`'s spec gives back the leaked mapping's cells to nobody.
- **Possible fixes**: `unix.Munmap(b)` before returning the `madvise` error, or ignore the hint's
  failure (it is only advice); removing the hint (etcd-io/bbolt#940, proposed in #939) removes
  the path.
- **Found**: 2026-10-12, the bbolt proof (`DB.close` after a failed `mmap`).
