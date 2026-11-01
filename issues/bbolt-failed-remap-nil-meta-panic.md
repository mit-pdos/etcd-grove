---
upstream: unchecked
---

# bbolt: a failed remap leaves `meta0`/`meta1` nil, and the next `Begin` panics

**Status**: a bug, a reachable panic after an environmental failure (a failed `munmap` or
`mmap` while a write transaction grows the mapping). minibolt (`examples/bboltfs/minibolt.go`)
has it too, by design: its `mmap`, `munmap`, `Get` and `Commit` are bbolt's.

**Where**: go.etcd.io/bbolt v1.5.0 `db.go`: `DB.mmap` (456) returns the error of `db.munmap()`
or of `mmap(db, size)` after `munmap`'s `invalidate` (557) has set `db.meta0 = db.meta1 = nil`;
`DB.meta` (1141) dereferences both (`db.meta1.Txid() > db.meta0.Txid()`). `tx.Commit` reaches
`mmap` through `allocate` when the high water mark passes the mapping, and only rolls back on
the error: the `DB` stays open. In minibolt: `DB.mmap` and `DB.munmap` (minibolt.go:149, 176),
`DB.meta` (191), read by `Get`/`Snapshot` under `metalock` and `mmaplock.RLock`.

**What happens**: a write transaction remaps; `munmap` succeeds or fails (either way `invalidate`
runs), or `munmap` succeeds and `mmap` fails (ENOMEM, ...). `mmap` returns the error and releases
`mmaplock`. Any `Begin` after that, or one already blocked on `mmaplock.RLock`, calls `db.meta()`
and panics with a nil dereference. In minibolt, a `Get` that took `metalock` before `Commit` sets
`failed` (minibolt sets it after `commit` returns, not under `mmaplock`) sees `failed == false`,
takes `mmaplock.RLock` and panics in `pickMeta(nil, nil)`; bbolt has no `failed` flag, so every
later transaction panics.

**Expected**: an error from the failed commit, and later transactions either served from a valid
mapping or refused with an error.

**How the proof handles it**: not yet. minibolt's `Get`/`Snapshot` specs
(`Spec/github_com/mit_pdos/etcd_grove/examples/bboltfs/DB__Get.lean`) are unprovable under the
model, in which `Munmap` and `Mmap` may fail (`Spec/golang_org/x/sys/unix/{Munmap,Mmap}.lean`):
the lock invariant of `mmaplock` cannot promise a reader a mapping.

**Possible fixes**: in minibolt, set `failed` (under `metalock`) before `mmap` releases
`mmaplock` on an error, or keep the old mapping until the new one is made (map first, then unmap
the old one), as bbolt does on Windows. In bbolt, the second: unmap only after the new `mmap`
succeeded, or mark the `DB` as unusable and make `meta()` return an error.

**Found**: 2026-11-01, designing the lock invariants of minibolt's proof (the `mmaplock` resource
must hold a mapping whenever a reader can take the read lock).
