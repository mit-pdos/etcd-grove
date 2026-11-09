---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# bbolt: a database file Open creates is never made durable in its directory

`bolt.Open` opens its path with `O_CREATE` (`db.go:234`, `:243`) and syncs the file's data and
size on every commit (`fdatasync`), but never syncs the directory that holds the new file's name.
POSIX makes a new name durable only by an `fsync` of its directory, so after a crash the whole
file may be gone, with every commit acknowledged before the crash: a first boot's database whose
`Update`s all returned nil can come back as no database at all.

**Why not an issue:** behavior etcd does not observe in practice: on journaled ext4
(`data=ordered`, the default) and on xfs, an `fsync`/`fdatasync` of a newly created file commits
the journal transaction that created its directory entry, so the name survives with the file's
first synced commit; etcd's data directory is also created and synced by `fileutil.TouchDirAll`
(`server/etcdserver/bootstrap.go:64-68, 211`), though not after the database file is added to it.
Other file systems (and POSIX as written) do not promise it. No test here: it needs a crash
simulation of the directory (found by reading OsFs's model, D4 of `notes/osfs-ext-plan.md`, where
a created file's name is not durable until its directory is synced). A first boot whose database
vanishes is recovered by etcd from its WAL (the consistent index restarts at 0), so etcd's
correctness does not rest on it, but only before the member's first local snapshot: after one, the
restart panics (`etcd-backend-name-lost-restart-panic.md`, found 2026-11-09).

## Proof

no: bbolt's specs record it in the client-owned state (`Spec/go_etcd_io/bbolt/Model.lean`,
`BoltSt.named`): a generation that starts from no file (or an empty file whose name may not be
durable: `boltFresh_alloc`) has `named = false`, and then a crash may leave no file, the empty
database (`BoltSt.recovers`). A client that needs every acknowledged commit durable from the first
boot creates the empty file and syncs its directory itself before `Open` (`fileHolds_new` then
takes it, `named = true`; A11-provability F1, `notes/specs-only/verify/repair-bbolt.md`).

## Notes

A fix in bbolt would be an `fsync` of the parent directory after `Open` creates the file (or
after `init` lays it out), as etcd's WAL does for its own files (`fileutil.Fsync` of the
directory in `wal.Create`).
