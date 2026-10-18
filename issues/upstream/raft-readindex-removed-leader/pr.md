Title: raft: fix stale read index at a leader that removed itself

The [single-voter shortcut](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1355-L1361) answers a `MsgReadIndex` at once when [`IsSingleton`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/tracker/tracker.go#L158-L162) holds, assuming, as both of their comments say, that the single voter is the leader calling it. `IsSingleton` does not guarantee that: it only counts the voters. A leader that removed itself stays leader unless `StepDownOnRemoval` is set, so it answers from its own commit index after the remaining voter has elected itself. This PR changes `IsSingleton` to take a node id and report whether that node alone is a quorum.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

This PR conflicts with #<other PR>, which fixes a related problem in the same lines; whichever merges second needs a rebase. I can combine both fixes in one PR if you prefer.

This PR was written in part with the assistance of AI; I have reviewed and tested every change.
