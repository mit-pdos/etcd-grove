---
upstream: none
checked: 2026-11-02
links:
blocks-proof: yes
---

# etcdserver: a restarted member can reissue its previous run's request ids if the clock went back

A member's request ids are its 16-bit member prefix and a counter seeded from the wall clock at
start (milliseconds, shifted by 8). If a member proposes request `X`, stops before applying it (the
entry stays in its WAL), and restarts with the clock behind where its previous run's counter had
reached (a clock step back, or more than 256 ids per millisecond on average before the stop), a new
request can get id `X`. When the replayed entry `X` is applied, its result is delivered to the new
request, which returns the old entry's response (or panics in the response's type assertion if the
kinds differ); the new request's own entry later triggers nothing.

**Why not an issue:** no test, found by code reading; it needs the wall clock to go back across a
restart (or a sustained 256 requests per millisecond), with an entry of the previous run still
unapplied. Same mechanism as
[`etcd-request-id-member-prefix`](etcd-request-id-member-prefix.md), across one member's runs
instead of two members.

## Proof

yes: the ids' freshness across a member's runs is the assumption of the trusted model of
`Generator.Next` (no other run of the member issued the id; the restart plan's R2c,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRestart.lean`, `notes/restart-plan.md`), which
etcd does not ensure.

## Notes

The code: `idutil.NewGenerator` (`pkg/idutil/id.go`), called at every start with `time.Now()`
(`server/etcdserver/server.go`), and `applyEntryNormal`'s `s.w.Trigger(id, ...)` for every entry
above the consistent index, replayed ones included. A test could promote it: start a member,
propose and stop before applying (`HardStop`), restart with a generator seeded earlier, and check
the response. A fix: seed the counter from the WAL (the highest id of the member's own entries, or
a persisted high-water mark), or from `max(now, last persisted)`.
