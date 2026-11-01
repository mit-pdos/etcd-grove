---
upstream: none
checked: 2026-10-16
links: []
blocks-proof: no
---

# lease: `Revoke` reads the range deleter without the lock that `SetRangeDeleter` and `Recover` write it under

`lessor.Revoke` releases `le.mu` after its map lookup and then reads `le.rd` twice without it,
while `SetRangeDeleter` and `Recover` write `le.rd` under `le.mu`: a `Revoke` concurrent with
either is a data race. The `Lessor` interface does not say they must not run concurrently.

**Why not an issue:** a precondition etcd meets: the server sets the range deleter once, at the
store's construction, and calls `Recover` and `Revoke` on the apply goroutine.

## Proof

no: `Revoke` is not proved yet; a proof would share the right to `le.rd` among the three methods,
held by the apply thread, which etcd meets.

## Notes

The test,
[`nonissues/etcd-lessor-revoke-rd-unlocked/revoke_rd_race_test.go`](etcd-lessor-revoke-rd-unlocked/revoke_rd_race_test.go)
(`server/lease`, `-race`), fails at etcd-io/etcd@1573d5941 (go1.27.3) with `-count=10` (not every
run): `WARNING: DATA RACE`, write at `lessor.go:271` (`SetRangeDeleter`), previous read at
`lessor.go:339` (`Revoke`). INDEX-reviewed.md's plan: non-issue.
