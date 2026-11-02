---
upstream: fixed
checked: 2026-11-02
links:
  - etcd-io/bbolt#362 pr merged: the fix, "Add protection when mmap somehow fails" (eabffad, 2023-01, in v1.3.7 and v1.5.0): Begin returns ErrInvalidMapping when the mapping is gone
blocks-proof: no
---

# bbolt: after a failed remap, the next transaction would dereference a nil meta page

A write transaction that grows the file past its mapping remaps it; if `munmap` or the new `mmap`
fails, `munmap`'s `invalidate` has already set the mapping and both meta pages to nil, and
`Commit` returns the error with the `DB` still open. A later `Begin` that called `db.meta()` would
dereference nil.

**Why not an issue:** fixed in bbolt since v1.3.7 (bbolt#362): `beginTx` and `beginRWTx` check
`db.data == nil` under `mmaplock` and return `ErrInvalidMapping`, so v1.5.0 (etcd's) returns an
error. The panic was only in this repository's minibolt (`examples/bboltfs/minibolt.go`), which
copied the remap without that check; and etcd stops on any failed commit anyway.

## Proof

no: bbolt has the check. minibolt, this repository's own example, needed it and has it now (`Get`
and `Snapshot` refuse with `errFailed` when they find no mapping,
`Proof/github_com/mit_pdos/etcd_grove/examples/bboltfs/DB.lean`); bbolt's old proof gave the
database up after a failed remap (`old/bbolt/notes/STATUS-bbolt.md`, `DBLost`).

## Notes

Checked 2026-11-02 at etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 with a failpoint test
(`mapError` during `Fill` past the mapping, then `View`): `View` returns `database isn't correctly
mapped`, no panic.
