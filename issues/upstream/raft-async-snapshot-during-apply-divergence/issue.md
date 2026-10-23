Title: With AsyncStorageWrites, entries applied after a snapshot that includes them diverge the state machine

### What happened?

With `AsyncStorageWrites`, the append thread applying each `MsgStorageAppend`'s snapshot ("snapshots to apply", `Config.AsyncStorageWrites`), and a state machine holding the data of the entries applied; voters 1, 2 and 3, node 1 leading:

1. Node 1 commits "a" at index 1; node 2 hands it to its apply thread in a `MsgStorageApply`.
2. Before the apply thread applies index 1, node 2 steps node 1's snapshot at index 2 (state "ab"); node 2's next `Ready` hands it to the append thread.
3. The append thread applies the snapshot (state "ab"); then the apply thread applies index 1 on top: state "aba".

The test below runs these steps through `RawNode`, with node 1's messages built by hand (output trimmed):

```
--- FAIL: TestRawNodeAsyncSnapshotDuringApply (0.00s)
        	Error:      	Not equal: 
        	            	expected: "ab"
        	            	actual  : "aba"
```

This affects any application with `AsyncStorageWrites` whose two threads run independently, as "Messages to different targets can be processed in any order" allows.

### What did you expect to happen?

Node 2's state should be "ab", the state at index 2: the snapshot should be applied after the entries handed out before it.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestRawNodeAsyncSnapshotDuringApply`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-async-snapshot-during-apply-divergence/rawnode_test.go#L967-L1044) on branch [`upamanyus/etcd-raft:fix/raft-async-snapshot-during-apply-divergence`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-async-snapshot-during-apply-divergence), off `main` (1931ff5be). On `main` it fails as above.

### Anything else we need to know?

An application avoids this if its append thread, before applying a snapshot, waits for the apply thread to finish every earlier `MsgStorageApply`. Is that required? If so, `Config.AsyncStorageWrites` should say so.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Raft version

<details>

`main` (1931ff5be), go1.26.9 linux/amd64.

</details>
