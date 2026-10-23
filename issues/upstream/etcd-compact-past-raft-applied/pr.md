Title: etcdserver: compact the raft log only after raft advances

After applying a batch of entries, [`applyAll`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/server.go#L986-L991) waits for the raft routine to persist them and then [compacts the raft log](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/server.go#L2144-L2150). The raft routine calls [`Advance`](https://github.com/etcd-io/etcd/blob/3aaab3479b6c4f5fe1b2b8f33437093c2caae88a/server/etcdserver/raft.go#L330-L336) only after that, so the compaction can pass raft's applied index, which [`MemoryStorage.Compact`](https://github.com/etcd-io/raft/blob/b867cf13f6bc0dae21204302df97bc2355c3af55/storage.go#L265-L267) forbids; a campaign in between [scans the log from the applied index](https://github.com/etcd-io/raft/blob/b867cf13f6bc0dae21204302df97bc2355c3af55/raft.go#L1002-L1018) and panics. This PR closes `raftAdvancedC` after every `Advance`, and `applyAll` waits for it before compacting.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
