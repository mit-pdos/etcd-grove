Title: raft: document that conf changes must be applied before Advance

[`Node.Advance`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/node.go#L166-L177) lets the application call `Advance` while it is still applying the last `Ready`, and [doc.go's step 4](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/doc.go#L101-L103) allows it "at any time after step 1". Raft's checks for a pending conf change, [before campaigning](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L995-L998) and [before accepting a conf change proposal](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1326), assume that every conf change up to the applied index has been applied; `Advance` moves the applied index whether or not `ApplyConfChange` has been called. This PR documents that a `Ready`'s conf changes must be applied before `Advance` (with `AsyncStorageWrites`, before a `MsgStorageApply`'s responses are delivered).

Fixes #<issue>

Written with the assistance of generative AI; I reviewed and tested every change.
