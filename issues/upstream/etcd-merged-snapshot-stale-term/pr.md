Title: etcdserver: drop a queued MsgSnap older than the applied term

raft makes a `MsgSnap` as leader of the message's term. [`processMessages`](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/raft.go#L374-L385) queues it, and a later apply job in [`applyAll`](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/server.go#L992-L998) replaces its snapshot with the data applied so far, keeping the message's term, assuming that data is no newer than that term. When raft steps down before the job runs, the data can be of a newer term. This PR drops a queued `MsgSnap` older than the last applied entry's term: raft has then left the message's term and reset its progress for every peer, so no leader waits for that message.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
