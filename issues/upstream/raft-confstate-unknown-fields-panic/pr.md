Title: raftpb: ignore unknown fields in ConfState.Equivalent

When raft restores a snapshot ([`restore`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1936)) or starts from storage ([`newRaft`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L479)), it panics unless the snapshot's `ConfState` is [`Equivalent`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raftpb/confstate.go#L26-L52) to the configuration it built from it. `Equivalent` compares sorted clones with [`proto.Equal`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raftpb/confstate.go#L48), which also compares unknown fields, and the built configuration has none. This PR clears the unknown fields of the clones before comparing them.

Fixes #<issue>

`TestRestoreFromSnapMsgUnknownField` runs the issue's example; it fails on `main` and passes with this change.

This PR was written in part with the assistance of AI; I have reviewed and tested every change.
