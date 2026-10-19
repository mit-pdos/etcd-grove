Title: raftpb: ignore unknown fields in ConfState.Equivalent

When raft restores a snapshot ([`restore`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1936)) or starts from its storage ([`newRaft`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L479)), it panics unless the snapshot's `ConfState` is [`Equivalent`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raftpb/confstate.go#L24-L52) to the configuration raft rebuilt from it, assuming, as `Equivalent`'s comment says, that it compares only the configurations its inputs describe. `Equivalent` compares the inputs with `proto.Equal`, which also compares unknown fields, and the rebuilt configuration has none. This PR makes `Equivalent` ignore unknown fields.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
