Title: raft: fix stale read index at a leader that removed itself

The [single-voter shortcut](https://github.com/etcd-io/raft/blob/1d3216d845a72ef5a78c55772ea220a931e2c3ef/raft.go#L2139-L2146) in `sendMsgReadIndexResponse` answers a `MsgReadIndex` at once when [`IsSingleton`](https://github.com/etcd-io/raft/blob/1d3216d845a72ef5a78c55772ea220a931e2c3ef/tracker/tracker.go#L158-L162) holds, assuming, as both of their comments say, that the single voter is the leader calling it. `IsSingleton` does not guarantee that: it only counts the voters. A leader that removed itself stays leader unless `StepDownOnRemoval` is set, so it answers from its own commit index after the remaining voter has elected itself. This PR adds `ProgressTracker.IsVoter` and takes the shortcut only when the leader is a voter.

Fixes #534

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
