---
upstream: none
checked: 2026-11-02
links:
blocks-proof: no
---
# raft: `doc.go` says `ApplyConfChange` must always be called; `Node` and `RawNode` say it must not be, for a rejected change

Two ways of rejecting a committed conf change are documented, and each passage forbids the
other's: [doc.go's step 3](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/doc.go#L92-L98)
says to zero the change's `NodeID` and call `ApplyConfChange` ("ApplyConfChange must be called one
way or the other"), while
[`Node.ApplyConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/node.go#L179-L183)
and [`RawNode.ApplyConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/rawnode.go#L108-L110)
say that for a rejected change "it must not be called". The `NodeID`-zero form does not work for a
`ConfChangeV2` leaving a joint configuration (it has no change to zero).

**Why not an issue:** documentation only, no test; both forms are sound in the code as long as
every replica decides the same for the same committed entry (a zero `NodeID` makes `confchange`
skip the change; no call leaves the configuration as it is). etcd follows doc.go
(`EtcdServer.applyConfChange` zeroes `NodeID` and calls `ApplyConfChange`,
[server/etcdserver/server.go](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/server.go#L2002-L2007)).

## Proof

no: the node API's rule admits both forms (`ConfRule`: per committed entry, a change applied,
which may be etcd's zeroed one, or a rejection without a call;
`Proof/go_etcd_io/raft/v3/ConfRule.lean`).

## Notes

A doc fix: make doc.go's step 3 say what `Node.ApplyConfChange` says, and that a change may also
be neutralized by zeroing `NodeID` (a `ConfChange`, or a `ConfChangeV2` with changes). Found
2026-10-28 by the spec review of raft's node API for `examples/kvreconf`
(`notes/spec-first-study/raft-node-unified-review-1.md`), which follows `node.go`
(`Replica.applyConf`). Upstream searched 2026-11-02 (`ApplyConfChange`, `ApplyConfChange reject`):
nothing.
