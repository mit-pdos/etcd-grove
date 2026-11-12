---
upstream: none
checked: 2026-11-09
links:
blocks-proof: no
---

# backend: defragmentation's deferred rollback dereferences a nil transaction if reopening the copy fails

`defragdb` (and the non-blocking defragmentation's `catchUpDefrag`) copies the database into a temporary one, committing the copy every `limit` entries and
beginning a new write transaction on it (`tmptx, reopenErr = tmpdb.Begin(true)`). If that `Begin`
failed, `tmptx` would be `nil`, the copy would return `reopenErr`, and the deferred
`tmptx.Rollback()` (run because the error is non-nil) would call `(*bolt.Tx).Rollback` on `nil`,
which reads `tx.managed` and panics.

**Why not an issue:** no test (code reading), and unreachable as etcd uses it: bbolt's
`Begin(true)` fails only when the database is opened read-only, not open, or has lost its mapping
(`beginRWTx`, `db.go:913-938`); the temporary database is opened read-write by defragmentation
itself, closed by no one else while the copy runs, and the commit just before succeeded (a failed
commit returns before the `Begin`), so its mapping is intact. `defragdbAndTrackLastKeys`, the
non-blocking bulk copy, already guards the same deferred call with `tmptx != nil`;
`catchUpDefrag` (`:969-977`, `:1004-1007`) does not.

## Proof

no: the backend's `Defrag` spec is trusted (names only); its "why it is true"
(`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__Defrag.lean`) excludes the failing
`Begin` by bbolt's `dbBroken_state` with the preceding commit's success (4c's specs), so the
deferred rollback always has a transaction.

## Notes

Code: `server/storage/backend/backend.go` (`defragdb`, the deferred rollback at `:805-809`, the
reassignment at `:839-842`), at the pinned fork `a4d2bb17`. A fix would guard the deferred call as
`defragdbAndTrackLastKeys` does (`if err != nil && tmptx != nil`). Found by the verification round's
bbolt completeness review (A11, S4).
