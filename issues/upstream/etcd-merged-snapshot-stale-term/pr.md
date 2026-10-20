Title: etcdserver: send a queued MsgSnap only while raft is at its term

raft makes a `MsgSnap` as leader of the message's term. [`processMessages`](https://github.com/etcd-io/etcd/blob/6782f5229b8a6dbc5f6d421107fd70d66de98694/server/etcdserver/raft.go#L374-L385) queues it, and a later apply job in [`applyAll`](https://github.com/etcd-io/etcd/blob/6782f5229b8a6dbc5f6d421107fd70d66de98694/server/etcdserver/server.go#L992-L998) replaces its snapshot with the data applied so far, keeping the message's term, assuming that data is no newer than that term. When raft steps down before the message is merged, it can be. This PR passes with each batch the term of the latest HardState raft has handed out, and `applyAll` drops a queued `MsgSnap` of an older term, for which raft, having reset its progress at the new term, no longer waits.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
