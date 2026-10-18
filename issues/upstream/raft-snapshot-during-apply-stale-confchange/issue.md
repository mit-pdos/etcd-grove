Title: A snapshot received while a conf change is being applied leaves a follower with the wrong configuration, or panics

### What happened?

With voters 1, 2 and 3, node 1 leading:

1. Node 1 commits "add 4" at index 1; node 2's `Ready` hands it out, and node 2's application starts applying it.
2. Before that application calls `ApplyConfChange` for "add 4", node 2 steps a snapshot from node 1 at index 2 (after "remove 4") with voters 1, 2 and 3. `Node` steps received messages while the application handles a `Ready`.
3. The application calls `ApplyConfChange` for "add 4", then `Advance`. Node 2 ends with voters 1, 2, 3 and 4, also after node 1 resends the snapshot.

With "add 4" entering a joint configuration and the snapshot taken in it, step 3 panics instead ("config is already joint"). The test below runs both cases through `RawNode`, with node 1's messages built by hand (output trimmed):

```
--- FAIL: TestRawNodeSnapshotDuringConfChangeApply (0.00s)
    --- FAIL: TestRawNodeSnapshotDuringConfChangeApply/0 (0.00s)
            	Error:      	Not equal: 
            	            	expected: []uint64{0x1, 0x2, 0x3}
            	            	actual  : []uint64{0x1, 0x2, 0x3, 0x4}
    --- FAIL: TestRawNodeSnapshotDuringConfChangeApply/1 (0.00s)
panic: config is already joint [recovered, repanicked]
```

This affects any follower that steps a snapshot between a `Ready` with a committed conf change and the `ApplyConfChange` call for it.

### What did you expect to happen?

In both cases node 2 should end with the snapshot's configuration, which already includes "add 4".

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestRawNodeSnapshotDuringConfChangeApply`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-snapshot-during-apply-stale-confchange/rawnode_test.go#L718-L764) on branch [`upamanyus/etcd-raft:fix/raft-snapshot-during-apply-stale-confchange`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-snapshot-during-apply-stale-confchange), off `main` (638f42739). On `main` it fails as above.

### Anything else we need to know?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
