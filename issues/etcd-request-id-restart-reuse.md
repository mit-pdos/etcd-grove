---
upstream: unchecked
---

# etcdserver: a restarted member can reissue its previous incarnation's request ids

- **Status**: an unstated precondition (request ids are unique only if the wall clock does not go
  backwards across a member's restart, and the previous incarnation's generator, started at
  millisecond t0, issues in all -- including after the restart, from handlers still running -- at
  most 256·(t1 − t0) ids, t1 the restart's millisecond: the new generator's first id,
  `prefix | (t1·256 + 1)`, is the old one's (256·(t1 − t0) + 1)-th. A restart within the
  millisecond of the previous start collides at the old generator's first id; Go's comment on
  `Generator` asks for a restart "after 1 ms", which is not enough by itself). Not reproduced yet. Same mechanism as
  [etcd-request-id-member-prefix](etcd-request-id-member-prefix.md), across one member's
  incarnations rather than two members.
- **Where** (the fork at the pin of `etc/goose.py`, `ab3c28d9a`):
  - `pkg/idutil/id.go`: `NewGenerator(memberID uint16, now time.Time)` sets the prefix
    `memberID << 48` and the suffix `lowbit(unixMilli(now), 40) << 8`; `Next` returns
    `prefix | lowbit(suffix++, 48)`.
  - `server/etcdserver/server.go:331`: `idutil.NewGenerator(uint16(b.cluster.nodeID), time.Now())`,
    at every start, so a restarted member's generator has its previous incarnation's prefix.
  - `applyEntryNormal` (`server.go`): `s.w.Trigger(id, ar)` for every entry above the consistent
    index, whoever proposed it, including the entries replayed from the WAL after a restart.
- **What happens**: a member proposes a request with id `X`. It stops before applying the entry
  (`HardStop`, or a crash), so the entry stays in its WAL above the backend's consistent index.
  The member restarts. If the wall clock is now earlier than when the previous incarnation's
  generator reached `X` (a clock step back, as NTP can make), the new generator's suffix range covers
  `X` again. A new client request then gets id `X` and registers a waiter for it. When the replayed
  entry `X` is applied, `Trigger(X, ...)` hands its result to the new request's waiter: the new
  request returns the old entry's response. That response may be of another kind, for which the
  type assertion in the request path panics, as in the cross-member case. The new request's own
  entry later triggers nothing.
- **Expected**: request ids unique across a member's restarts, or the precondition documented.
- **How the proof handles it**: as an assumption in the semantics, where it is used (the restart
  plan's R2c stage 2, 2026-11-02): the cluster's id state is keyed by a member's incarnation
  (`Proof/go_etcd_io/etcd/pkg/v3/idutil/Defs.lean`), and `Generator.Next` is a trusted model
  (`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`) whose Go body is followed, before the return, by
  Perennial's `assume` of the issue record's `"Issue"` (`GooseLang/Ext/IdIssue`, model-only state):
  no other generator issued the id -- this issue's precondition. A false `Assume` does not return, so the model excludes the
  clashing executions; nothing in the logic states it (a first draft's logical statement was
  refutable). It is not a premise of the example's theorem: as for the read-write mutex's reader
  limit (`/shared/grove-paper/sosp26/rwmutex.tex`), the specs stay free of the limit. Across members,
  ids stay distinct by prefix, proved.
- **Possible fixes**: seed the suffix from the WAL (the highest id of the member's own entries, or
  a persisted high-water mark) instead of the clock; or take `max(now, last persisted)`.
- **Found**: 2026-11-02, drafting `examples/restart3`'s specs (the restart plan's R2).
