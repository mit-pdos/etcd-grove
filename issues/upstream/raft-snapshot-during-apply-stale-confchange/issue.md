Title: A snapshot received while a conf change is being applied leaves a follower with the wrong configuration, or panics

On `main` (c51f010, go1.26.10 linux/amd64), a follower that steps a snapshot while its application is still applying a committed conf change applies that conf change again, on top of the snapshot's configuration, which already includes it. With voters 1, 2 and 3, node 1 leading:

1. Node 1 commits "add 4" at index 1; node 2's `Ready` hands it out, and node 2's application starts applying it.
2. Before node 2's application calls `ApplyConfChange` for "add 4", node 2 steps a snapshot from node 1 at index 2, taken after "remove 4", with voters 1, 2 and 3.
3. Node 2's application calls `ApplyConfChange` for "add 4", then `Advance`, then applies the snapshot from the next `Ready`. Node 2 ends with voters 1, 2, 3 and 4, and keeps them after node 1 resends the snapshot.

When "add 4" enters a joint configuration and the snapshot is taken in it, step 3 panics instead ("config is already joint"). In both cases node 2 should end with the snapshot's configuration.

[`restore`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1915-L1928) switches the follower to the snapshot's configuration as soon as the follower steps the snapshot, which [`Node` does while the application is still applying the last `Ready`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/node.go#L394-L399). [`applyConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1943-L1963) applies the change it is given to the current configuration, assuming that configuration is the one just before the change. After the restore, the current configuration is the snapshot's, so "add 4" is applied a second time; in the joint case, entering a joint configuration from one that is already joint panics. Nothing corrects the configuration afterwards: applying the snapshot from the `Ready` does not, and [`restore` ignores the resent snapshot](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1853-L1855), which is no longer above the commit index. This affects any follower that steps a snapshot between a `Ready` with a committed conf change and the `ApplyConfChange` call for it.

Unit test: [`TestRawNodeSnapshotDuringConfChangeApply`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-snapshot-during-apply-stale-confchange/rawnode_test.go#L718-L788) on branch [`upamanyus/etcd-raft:fix/raft-snapshot-during-apply-stale-confchange`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-snapshot-during-apply-stale-confchange), off `main` (c51f010), runs both cases through `RawNode`, with node 1's messages built by hand. On `main` it fails (output trimmed):

```
--- FAIL: TestRawNodeSnapshotDuringConfChangeApply (0.00s)
    --- FAIL: TestRawNodeSnapshotDuringConfChangeApply/0 (0.00s)
            	Error:      	Not equal: 
            	            	expected: []uint64{0x1, 0x2, 0x3}
            	            	actual  : []uint64{0x1, 0x2, 0x3, 0x4}
    --- FAIL: TestRawNodeSnapshotDuringConfChangeApply/1 (0.00s)
panic: config is already joint [recovered, repanicked]
```

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
