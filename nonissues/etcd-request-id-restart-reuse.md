---
upstream: none
checked: 2026-11-02
links:
blocks-proof: no
---

# etcdserver: a restarted member can reissue its previous run's request ids if the clock went back

A member's request ids are its 16-bit member prefix and a counter seeded from the wall clock at
start (milliseconds, shifted by 8). If a member proposes request `X`, stops before applying it (the
entry stays in its WAL), and restarts with the clock behind where its previous run's counter had
reached, a new request can get id `X`: the previous run's generator, started at millisecond t0,
issues in all (including after the restart, from handlers still running) more than 256·(t1 − t0)
ids, t1 the restart's millisecond, so the new generator's first id `prefix | (t1·256 + 1)` is the
old one's (256·(t1 − t0) + 1)-th. A clock step back gives it, and so does a restart within the
millisecond of the previous start (a collision at the old generator's first id); Go's comment on
`Generator` asks for a restart "after 1 ms", which is not enough by itself. When the replayed entry `X` is applied, its result is delivered to the new
request, which returns the old entry's response (or panics in the response's type assertion if the
kinds differ); the new request's own entry later triggers nothing.

**Why not an issue:** no test, found by code reading; it needs the wall clock to go back across a
restart, or more ids than 256 per millisecond since the previous start, with an entry of the
previous run still unapplied. Same mechanism as
[`etcd-request-id-member-prefix`](etcd-request-id-member-prefix.md), across one member's runs
instead of two members.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; the ids' freshness across a member's runs is the assumption of the trusted model of
`Generator.Next` (`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`: its Go body, then Perennial's
`assume` of the issue record's `"Issue"`, `GooseLang/Ext/IdIssue`: no other generator issued the
id; the cluster's id state keyed by a member's incarnation, `Proof/go_etcd_io/etcd/pkg/v3/idutil/Defs.lean`;
the restart plan's R2c stage 2, `notes/restart-plan.md`), which etcd does not ensure.

## Notes

The code: `idutil.NewGenerator` (`pkg/idutil/id.go`), called at every start with `time.Now()`
(`server/etcdserver/server.go`), and `applyEntryNormal`'s `s.w.Trigger(id, ...)` for every entry
above the consistent index, replayed ones included. A test could promote it: start a member,
propose and stop before applying (`HardStop`), restart with a generator seeded earlier, and check
the response. A fix: seed the counter from the WAL (the highest id of the member's own entries, or
a persisted high-water mark), or from `max(now, last persisted)`.
