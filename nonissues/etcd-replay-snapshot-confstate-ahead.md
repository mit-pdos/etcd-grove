---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# etcdserver: a raft snapshot taken while replaying the WAL after a restart records a configuration later than its index

After a restart, etcd sets the configuration it records in raft snapshots (`ep.confState`) to the
backend's membership, which is the membership at the backend's consistent index `c`
([bootstrap.go:107-116](https://github.com/etcd-io/etcd/blob/a4d2bb1720b9/server/etcdserver/bootstrap.go#L107-L116),
[server.go:803-807](https://github.com/etcd-io/etcd/blob/a4d2bb1720b9/server/etcdserver/server.go#L803-L807)),
while its applied index starts at the WAL snapshot's index `s`. The entries in `(s, c]` are replayed
without passing their configuration changes to raft or to `ep.confState`
([server.go:2052](https://github.com/etcd-io/etcd/blob/a4d2bb1720b9/server/etcdserver/server.go#L2052)).
An in-memory snapshot (every 100 applied entries) or a disk snapshot taken during that replay, at
an applied index `a` in `(s, c)`, therefore records the configuration at `c` with the log at `a`
([server.go:2132](https://github.com/etcd-io/etcd/blob/a4d2bb1720b9/server/etcdserver/server.go#L2132)).
When a configuration change lies in `(a, c]`, the snapshot's `ConfState` is not the configuration at
its index. A follower restoring it, then applying the entries after `a`, would apply that change a
second time.

**Why not an issue:** no test, found by code reading (by the R1 completeness review, 2026-11-09).
No wrong result was found in etcd's own flow: a leader never sends its storage's snapshot as is (every
`MsgSnap` is replaced by the merged snapshot message, `createMergedSnapshotMessage`, whose
configuration is the one at the applied index once the replay is over), and a later restart
rebuilds the configuration from the backend again.

## Proof

no: raft's node API takes a snapshot's configuration at any committed point at or after its index
(`Spec/go_etcd_io/raft/v3/Api.lean`, `snap_make.spec`; a node installing it takes that
configuration and re-applies nothing below it), so etcd's snapshot is admitted. Whether raft's own
proof can carry a configuration ahead of the log is R2's obligation, and an open question for the
user (`notes/specs-only/batch-R1.md`, round 1).

## Notes

Reachable without a crash: a graceful restart with a member change among the last `SnapshotCount`
(10000) entries before it. Recording the configuration at the applied index during the replay
(tracking the replayed changes in `ep.confState`) would remove the question.
