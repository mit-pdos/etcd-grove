Title: raft: refuse an empty joint conf change in a joint config

In a joint config, [`stepLeader`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1326-L1337) accepts any conf change without changes, assuming, as `wantsLeaveJoint` says, that such a conf change leaves the joint config. But [`applyConfChange`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raft.go#L1957-L1967) leaves only if [`LeaveJoint`](https://github.com/etcd-io/raft/blob/638f42739b77572b5708eb0d8a776a272ade71ed/raftpb/confchange.go#L108-L114) holds (no changes, `Auto` transition); with a joint transition it enters a joint config again, which fails with "config is already joint", and panics. This PR makes the leader accept a conf change in a joint config only if `LeaveJoint` holds; outside one, empty conf changes are refused as before.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

Written with the assistance of generative AI; I reviewed and tested every change.
