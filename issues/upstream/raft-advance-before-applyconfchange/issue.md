Title: Calling Advance before applying a conf change, which Node.Advance allows, commits two different entries at one index

### What happened?

With voters 1, 2 and 3, node 1 leading, and node 1's application calling `Advance` before it applies a `Ready`'s committed entries, which `Node.Advance` allows:

1. Node 1 commits "remove 2" at index 2. Node 1's application calls `Advance` but not yet `ApplyConfChange`; nodes 2 and 3 apply it.
2. Node 1 accepts "remove 1" and commits it at index 3, still with voters 1, 2 and 3. Nodes 2 and 3 apply it, leaving node 3 the only voter in their configuration.
3. With node 3 cut off, node 1 commits `x` at index 4 with node 2.
4. Node 3 becomes leader on its own and commits its empty entry at index 4.

The test below runs these steps through `Node` (output trimmed):

```
--- FAIL: TestNodeAdvanceBeforeApplyConfChange (1.03s)
        	Error:      	Not equal: 
        	            	expected: "1/4 EntryNormal \"x\""
        	            	actual  : "2/4 EntryNormal \"\""
        	Messages:   	index 4 committed on nodes 1 and 3
```

This affects any application that calls `Advance` before `ApplyConfChange` (doc.go's step 4: "at any time after step 1") and makes two membership changes in a row.

### What did you expect to happen?

Index 4 should not be committed with two different entries.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestNodeAdvanceBeforeApplyConfChange`](https://github.com/upamanyus/etcd-raft/blob/repro/raft-advance-before-applyconfchange/node_test.go#L1063-L1150) on branch [`upamanyus/etcd-raft:repro/raft-advance-before-applyconfchange`](https://github.com/upamanyus/etcd-raft/tree/repro/raft-advance-before-applyconfchange), off `main` (1931ff5be). On `main` it fails as above.

### Anything else we need to know?

If node 1's application calls `ApplyConfChange` before `Advance`, node 1 does not commit `x`. Is that order required? If so, `Node.Advance` and doc.go should say so.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Raft version

<details>

`main` (1931ff5be), go1.26.9 linux/amd64.

</details>
