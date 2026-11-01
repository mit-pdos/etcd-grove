---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/raft#370 pr merged: related, where it starts: allows the index-0 ConfState-only snapshot (for etcd's restart from its v3 store, etcd-io/etcd#21138); the discussion does not consider nodes added later
blocks-proof: no
---
# raft: with the initial configuration only in an index-0 snapshot, a node added later can win an election alone

If a cluster's nodes start from an index-0 snapshot holding only the initial `ConfState` (which
`MemoryStorage.ApplySnapshot`'s comment allows), a node added later with empty storage is caught up
by `MsgApp` from index 1, never by snapshot, and applies the log's conf changes to its own empty
configuration. After its own `add` its configuration is itself alone: cut off, it wins an election
on its own vote and commits a different entry at an index the cluster already committed.

**Why not an issue:** a precondition of how an application bootstraps a cluster, which etcd and
raft's documented paths meet: a new etcd cluster starts with `StartNode` and peers
(`server/etcdserver/bootstrap.go`), so the initial configuration is in the log; the README starts
a cluster the same way, and `RawNode.Bootstrap`'s doc recommends a manual bootstrap with first
index > 1, where a joiner is caught up by snapshot. The index-0 snapshot of etcd-io/raft#370 is
used by etcd only at restart, when the log still holds the conf entries. At most worth
documenting (INDEX-reviewed.md's Plan: "Nonissue, maybe some documentation would help").

`TestJoinerWithoutBootstrapConfState` in
[`nonissues/raft-joiner-empty-confstate/joiner_empty_confstate_test.go`](raft-joiner-empty-confstate/joiner_empty_confstate_test.go)
(public `RawNode` API, conf changes applied before `Advance`) fails at etcd-io/raft@c51f010c851e,
go1.27.3:

```
joiner_empty_confstate_test.go:128: node 1 config voters=(1 2 3 4); node 4 config voters=(4)
joiner_empty_confstate_test.go:146: index 3 committed as "x" (term 1) on node 1 and as "" (term 2) on node 4
--- FAIL: TestJoinerWithoutBootstrapConfState (0.00s)
```

## Proof

no: the reconfiguration paper proof assumes every node starts from `c0`
(`notes/reconfiguration-safety.md`, section 0), which etcd's bootstrap meets; the scope must say
how `c0` is set up (`notes/reconfiguration-safety-review.md`).

## Notes

The restart analogue (`Config.Applied` past a conf entry newer than the stored `ConfState`) was not
reproduced. `raft-conf-lag-model/leaderlag_test.go` sets node 4 up this way too; its control claim
holds only because node 4 never campaigns there.
