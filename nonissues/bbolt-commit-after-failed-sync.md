---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/bbolt#1311 pr merged: a commit whose meta write fails frees pages readers still see (a different failed-commit path; the fork carries it)
blocks-proof: no
---

# bbolt: a commit that succeeds after a failed sync can leave a database a crash corrupts

After an `fdatasync` of the database file fails (an explicit `DB.Sync`, a failed commit's data or
meta sync, or `grow`'s sync), Linux marks the dirty pages clean without writing them, and no later
sync writes them unless they are rewritten. A program that keeps using the database can then
commit successfully (`Commit` returns nil after its own syncs succeed) a tree whose meta page is
on disk but which reaches pages whose earlier writes were dropped; a crash afterwards leaves a
database that opens to stale pages (wrong data, or a panic on a malformed page). Two runs: a
concurrent `DB.Sync` fails while a commit's data pages are dirty, then the commit's own syncs
succeed; or a commit's meta sync fails (the commit is kept), the next writer reuses pages the
on-disk meta still reaches, and a crash recovers that older meta over overwritten pages.

**Why not an issue:** a precondition etcd meets: etcd exits on any commit error
(`server/storage/backend/batch_tx.go:302`, `lg.Fatal`) and syncs only its defragmentation copy,
fatally on an error (`backend.go:578-581`); bbolt documents nothing about continuing after a sync
error, and the general answer (PostgreSQL's "fsyncgate", 2018) is that an fsync error must be
treated as fatal for the data written since the last good sync. No test here: it needs fault
injection in `fdatasync` and a crash (found by reasoning about OsFs's model of a failed sync, D2 of
`notes/osfs-ext-plan.md`, which follows Linux).

## Proof

no: bbolt's specs record a failed sync in the client-owned state (`Spec/go_etcd_io/bbolt/Model.lean`,
`BoltSt.lost`), after which a commit promises nothing about what a crash recovers
(`BoltSt.commit`/`attempt` set `dur := none`); clients that stop at the first error, as etcd and
the bank test do, never reach that state.

## Notes

A fix in bbolt would be to make the database unusable after a failed sync (as `ErrInvalidMapping`
does after a failed remap), or to resync every page reachable from the current meta.
