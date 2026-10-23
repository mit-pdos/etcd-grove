Title: raft: apply a snapshot after earlier entries with async writes

With `AsyncStorageWrites`, [`restore`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1852-L1856) accepts a snapshot while committed entries handed out earlier in a `MsgStorageApply` are still being applied, and the [next `Ready`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/rawnode.go#L155-L169) hands the snapshot to the append thread. The two threads [may process their messages in any order](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L162-L179), so the older entries can be applied on top of the snapshot. Raft [holds back committed entries while a snapshot is pending](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/log.go#L253-L258), but not a snapshot while committed entries are being applied. This PR makes `RawNode` hand nothing to the append thread while a snapshot waits for those entries to be applied.

Fixes #<issue>

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

This PR's `RawNode` change is also part of #<other PR>, which needs it with `AsyncStorageWrites`; the two merge cleanly in either order. I can combine both fixes in one PR if you prefer.

Written with the assistance of generative AI; I reviewed and tested every change.
