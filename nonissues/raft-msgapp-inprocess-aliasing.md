---
upstream: none
checked: 2026-11-09
links:
blocks-proof: no
---
# raft: a stepped `MsgApp`'s entries slice is adopted, so its spare capacity must belong to the receiver

A follower handling a `MsgApp` keeps the message's `Entries` slice itself as its unstable log when
the entries start at or before its unstable offset (`u.entries = ents`,
[log_unstable.go](https://github.com/etcd-io/raft/blob/b867cf13/log_unstable.go#L206-L212)), and a
later `MsgApp` that continues the log appends to it in place (`append(u.entries, ents...)`, line
205), writing into the slice's spare capacity. So whatever backs that capacity is written by the
follower. If the stepped message shares its backing array with memory another node still uses (an
in-process transport handing the follower the leader's own `*pb.Message`, or a hand-built message
whose `Entries` is a sub-slice of a longer array), the follower overwrites it, and the two nodes
race on it.

**Why not an issue:** a precondition etcd meets, found by code reading, no test. rafthttp gives the
receiver a fresh decode of every message (protobuf's unmarshalling allocates the slice), and
raft's own `MsgApp`s carry slices with no spare capacity: `raftLog.slice` clips what it returns
([log.go:510](https://github.com/etcd-io/raft/blob/b867cf13/log.go#L507-L510); the mixed path
allocates exactly in `extend`), provided the `Storage`'s `Entries` protects its array as its
documentation asks (`MemoryStorage` returns `ents[:len(ents):len(ents)]`,
[storage.go:165](https://github.com/etcd-io/raft/blob/b867cf13/storage.go#L161-L165)). The hazard
needs an in-process transport stepping a message with spare capacity it does not own: a `Storage`
that breaks the documented `Entries` contract, or a hand-built `MsgApp`. raft's documentation does not
say that `Step` may keep and append to the message's entries slice.

## Proof

no: the premise `msgRecv ml m` of `node.Step.spec` and `RawNode.Step.spec` (and `raft.Step`'s
`stepMsg` for a `MsgApp`): a stepped message owns its `Entries` slice's spare capacity. rafthttp's
decoders and `proto.Clone` give it (requested of 2f's `recvd` and 2a's `Unmarshal`/`Clone`); the
in-process snippets clone before stepping (`examples/specreq/raftnode/transport.go`, `ReqDeliver`).
Alternative, open for the user: the fork clips the slice in `logSliceFromMsgApp`
(`slices.Clip(m.GetEntries())`), after which no stepped message needs its capacity.
