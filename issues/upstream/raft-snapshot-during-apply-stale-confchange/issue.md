Title: A follower that receives a snapshot while applying a conf change ends with a configuration that is not the snapshot's

### What happened?

A follower's `Ready` hands out a committed conf change "add 4" (index 1). If the follower steps a `MsgSnap` at index 2 with voters `[1 2 3]` (after "remove 4") before the application calls `ApplyConfChange("add 4")`, it ends with voters `[1 2 3 4]`; if the snapshot arrives after `Advance`, with `[1 2 3]`:

```
--- FAIL: TestRawNodeSnapshotDuringConfChangeApply (0.00s)
    --- FAIL: TestRawNodeSnapshotDuringConfChangeApply/snapBeforeApply=true (0.00s)
            	Error:      	Not equal: 
            	            	expected: []uint64{0x1, 0x2, 0x3}
            	            	actual  : []uint64{0x1, 0x2, 0x3, 0x4}
```

This affects any follower stepping a snapshot that covers a conf change not yet passed to `ApplyConfChange`, as `Node` can while it waits for `Advance`.

### What did you expect to happen?

The follower ends with the snapshot's voters `[1 2 3]` in both cases.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestRawNodeSnapshotDuringConfChangeApply`](https://github.com/upamanyus/etcd-raft/blob/raft-snapshot-during-apply-stale-confchange/rawnode_test.go) on branch [`upamanyus/etcd-raft:raft-snapshot-during-apply-stale-confchange`](https://github.com/upamanyus/etcd-raft/tree/raft-snapshot-during-apply-stale-confchange), off `main` (638f42739). On `main` the `snapBeforeApply=true` case fails as above.

### Anything else we need to know?

With a joint conf change instead of "add 4", the same sequence panics with "config is already joint" (reproduced with a test that is not on the branch).

Which fix do you prefer: ignore a snapshot while committed entries are being applied (the linked PR), make `ApplyConfChange` skip conf changes a restored snapshot covers, or forbid `Step` between `Ready` and `Advance`?

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
