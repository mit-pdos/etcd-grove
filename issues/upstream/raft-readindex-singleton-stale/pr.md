Title: raft: fix stale read index at a new single-voter leader

A leader postpones a `MsgReadIndex` until it has committed an entry in its term ([`stepLeader`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1363-L1368)), but the [single-voter shortcut](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1355-L1361) answers before that check, so a new leader of a configuration a removal reduced to itself can answer below entries the previous leader committed. This PR moves the shortcut into [`sendMsgReadIndexResponse`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L2146-L2162), which runs after that check and which postponed requests also go through.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

This PR conflicts with #<other PR>, which fixes a related problem in the same lines; whichever merges second needs a rebase. I can combine both fixes in one PR if you prefer.

Written with the assistance of generative AI; I reviewed and tested every change.
