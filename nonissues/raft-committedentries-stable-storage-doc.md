---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/raft#8 pr merged: related, not this bug: asynchronous storage writes, which introduced allowUnstable and its comment in log.go and left the Ready.CommittedEntries comment as it was
blocks-proof: no
---
# raft: `Ready.CommittedEntries` says its entries "have previously been appended to stable storage", which the synchronous mode contradicts

[`Ready.CommittedEntries`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/node.go#L89-L91)
says its entries "have previously been appended to stable storage", but without
`AsyncStorageWrites` (etcd's setting) `RawNode` hands out committed entries from the unstable log
([rawnode.go](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/rawnode.go#L440-L445),
[log.go](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/log.go#L216-L219):
"Entries can be committed even when the local raft instance has not durably appended them"), so a
`Ready` may carry an entry in both `Entries` and `CommittedEntries`. An application that trusts the
comment and calls `MemoryStorage.CreateSnapshot` at a committed index before appending the
`Ready`'s entries panics ("snapshot ... is out of bound lastindex",
[storage.go](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/storage.go#L250-L252)).

**Why not an issue:** documentation only, no test; doc.go's usage steps (append, then apply) avoid
it, and etcd handles exactly this: its apply loop may apply entries before the raft loop has saved
them, but waits for the save before snapshotting ("or applied index might be greater than the last
index in raft storage",
[server/etcdserver/server.go](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/server.go#L986-L991)).

## Proof

no: the specs never derive "held by the storage" from "committed and delivered":
`MemoryStorage.CreateSnapshot.spec` takes a delivered bound given by the append receipt and by
`Advance` (`Spec/go_etcd_io/raft/v3/MemoryStorage__CreateSnapshot.lean`).

## Notes

A doc fix: "In the synchronous mode, these may include entries of this `Ready`'s `Entries`: append
those first (see doc.go)." Found 2026-10-28 by spec review 9 of the unified node API
(`notes/spec-first-study/raft-node-unified-review-9.md`). Upstream searched 2026-11-02
(`CommittedEntries stable storage`; PRs on `CommittedEntries`): only #8.
