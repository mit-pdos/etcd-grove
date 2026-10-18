Title: raft: fix stale read index with a single voter

A leader postpones a `MsgReadIndex` until it commits an entry at its term ([`stepLeader`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1363-L1368)), but the [single-voter shortcut](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1355-L1361) answers before that check, and [`IsSingleton`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/tracker/tracker.go#L158-L162) does not check that the single voter is the leader. So a new leader of a configuration reduced to itself can answer below entries the previous leader committed, and a leader that removed itself keeps answering when deposed. This PR moves the shortcut into [`sendMsgReadIndexResponse`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L2146-L2162), which runs after that commit, and changes `IsSingleton` to take the node's id, so that the shortcut is taken only by the only voter.

Fixes #<issue>

The first commit adds tests for both cases, which fail on `main`; the second, the fix, makes them pass.

This PR was written in part with the assistance of AI; I have reviewed and tested every change.
