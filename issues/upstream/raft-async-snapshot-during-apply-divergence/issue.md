Title: With AsyncStorageWrites, entries applied after a snapshot that includes them diverge the state machine

On `main` (1931ff5be, go1.26.9 linux/amd64), with `AsyncStorageWrites`, a follower's append thread can install a snapshot before the follower's apply thread has applied committed entries that the snapshot includes; the apply thread then applies them again, on top of the snapshot. With voters 1, 2 and 3, node 1 leading, node 2's append thread installing each `MsgStorageAppend`'s snapshot in the state machine ("snapshots to apply", in `Config.AsyncStorageWrites`), and a state machine holding the data of the entries applied:

1. Node 1 commits "a" at index 1; node 2 hands it to its apply thread in a `MsgStorageApply`.
2. Before node 2's apply thread applies index 1, node 2 steps node 1's snapshot at index 2, with state "ab"; node 2's next `Ready` hands the snapshot to its append thread.
3. Node 2's append thread installs the snapshot (state "ab"); then node 2's apply thread applies index 1 on top of it: state "aba".

Node 2's state should be "ab", the state at index 2: the snapshot should be installed after the entries handed out before it.

Raft keeps this order in one direction only. While a snapshot is pending, [raft hands out no new committed entries](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/log.go#L253-L258) ("Doing so raises questions about what should be applied first"). Nothing holds a snapshot back for the entries already handed out: [`restore`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1852-L1855) accepts any snapshot above the commit index, even while entries from an earlier `MsgStorageApply` are still being applied, and the [next `Ready`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/rawnode.go#L155-L169) puts the snapshot in a `MsgStorageAppend` at once. The append thread and the apply thread [may process their messages in any order](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L162-L179), so the snapshot can be installed first. This affects any application with `AsyncStorageWrites` whose two threads run independently.

Unit test: [`TestRawNodeAsyncSnapshotDuringApply`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-async-snapshot-during-apply-divergence/rawnode_test.go#L967-L1044) on branch [`upamanyus/etcd-raft:fix/raft-async-snapshot-during-apply-divergence`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-async-snapshot-during-apply-divergence), off `main` (1931ff5be), runs these steps through `RawNode`, with node 1's messages built by hand. On `main` it fails (output trimmed):

```
--- FAIL: TestRawNodeAsyncSnapshotDuringApply (0.00s)
        	Error:      	Not equal: 
        	            	expected: "ab"
        	            	actual  : "aba"
```

An application avoids this if its append thread waits for its apply thread to finish every earlier `MsgStorageApply` before installing a snapshot. Is that required? If so, `Config.AsyncStorageWrites` should say so.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
