Title: etcdserver: drop a queued MsgSnap older than the applied term

raft makes a `MsgSnap` as leader of the message's term. [`processMessages`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/raft.go#L374-L385) queues it, and a later apply job in [`applyAll`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/server.go#L992-L998) replaces its snapshot with the data applied so far but keeps the message's term. When raft steps down before the job runs, that data can be of a newer term, and a follower still at the message's term that installs it has a log term above its current term. This PR drops a queued `MsgSnap` older than the last applied entry's term: raft has then left that term and reset every peer's progress, so no leader waits for the message.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
