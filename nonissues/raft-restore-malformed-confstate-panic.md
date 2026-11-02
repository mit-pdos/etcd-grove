---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/raft#546 issue open: related, not this bug: DescribeSnapshot and DescribeConfState panic on a nil ConfState
blocks-proof: no
---
# raft: a node restarted from a malformed `ConfState` panics in `newRaft`

`newRaft` restores the configuration from `Storage.InitialState`'s `ConfState` and panics, through
the logger, when the restored configuration does not round-trip to it
([raft.go](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L471-L479),
`assertConfStatesEquivalent`). `confchange.Restore` accepts `ConfState`s that do not round-trip: a
repeated id (`Voters: [1, 1]` restores to `[1]`), or `AutoLeave: true` with no `VotersOutgoing`
(the restored configuration is not joint). Neither `Storage.InitialState` nor `Config.Storage`
says what form the `ConfState` must have.

**Why not an issue:** a malformed storage input, found by code reading, no test: the `ConfState`s
etcd stores come from raft (`ApplyConfChange`), which produces neither form. At most a doc
sentence on `Storage.InitialState` (a `ConfState` raft produced, or at least without repeated ids
and with `AutoLeave` only when joint), or an error from `newRaft` instead of a panic.

## Proof

no: `newRaft.spec` and `NewRawNode.spec` take `ConfStateOk` (`Spec/go_etcd_io/raft/v3/newRaft.lean`,
`Spec/go_etcd_io/raft/v3/NewRawNode.lean`), which `RestartNode` obtains from the storage's
invariant (`Proof/go_etcd_io/raft/v3/RestartNode.lean`), so the node API is unchanged.

## Notes

Found 2026-11-02 by the durability proof (stage II(r), `notes/raft-durable-backtracking.md`). Not
run: a test would be a `MemoryStorage` whose snapshot metadata holds `Voters: [1, 1]`, then
`NewRawNode(&Config{ID: 1, Storage: s, ...})`, expected to panic. Upstream searched 2026-11-02
(`ConfState Equivalent`, `ConfState panic`): only #546.
