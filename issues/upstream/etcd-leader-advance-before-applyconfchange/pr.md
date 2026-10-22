Title: etcdserver: apply conf changes before Advance on the leader too

The [raft loop](https://github.com/etcd-io/etcd/blob/7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b/server/etcdserver/raft.go#L297-L331) waits for the apply loop before calling `Advance` when a `Ready` commits a conf change, but only on a follower or candidate. raft's check before accepting a conf change proposal [compares the pending conf change with the applied index](https://github.com/etcd-io/raft/blob/b867cf13f6bc0dae21204302df97bc2355c3af55/raft.go#L1326), which `Advance` moves, so until the leader's apply loop calls `ApplyConfChange` the leader accepts a second conf change while it still uses the configuration before the first. This PR makes the leader wait as the follower does.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
