---
upstream: none
checked: 2026-11-25
links:
  - etcd-io/etcd#14352 issue closed: a different failure to restart (an OOM-killed member), related only by the "database file of the backend is missing" message
blocks-proof: no
---

# etcd: a restart without `db` renames the WAL snapshot's `.snap.db` onto `db`, then deletes it

When `member/snap/db` is missing at a restart (a WAL exists) and the snapshot directory holds the `.snap.db` of
the WAL's newest valid snapshot, `bootstrap` creates an empty `db`, finds its consistent index `0` below the
snapshot's, and `OpenSnapshotBackend` renames `<j>.snap.db` onto `db` and opens it
(`server/etcdserver/bootstrap.go:305-331`, `:499-556`; `server/storage/backend.go:65-80`). `Finalize` then sees
`beExist` false and a v3 cluster version (now read from the recovered database) and runs `os.RemoveAll(db)` and
returns "database file (…) of the backend is missing" (`bootstrap.go:558-579`). The recovered database, the one copy
of the snapshot's data on the member, is gone; the next start finds neither `db` nor `<j>.snap.db` and panics in
`recoverSnapshot` (`failed to recover v3 backend from snapshot`: `ErrNoDBSnapshot`, `bootstrap.go:532`).

**Why not an issue:** found by code reading (fork `e94f33b50`, the same code on upstream main), no test; it needs
`db` removed from outside etcd (a crash never leaves `db` absent beside a WAL with a snapshot: the install's rename is
atomic, and the fork's `removeBackendDurably` removes it only beside an unsaved WAL). The member is lost either way
(without the `.snap.db` the first start already panics); the removal only destroys data an operator could have
copied back. Upstream's `RemoveAll` targets the empty `db` the same start created; it did not foresee the rename.

## Proof

no: `bootstrapCrashContract`'s `.snap.db` case (`etcdserver/InvCrashImage.lean`) allows `db` absent (`fileHolds`
with `D = ∅`), and its post admits the error (`notes/axiom-review/c-i2-snapdb.md`, attack 7); the crash images never
have `db` absent.
