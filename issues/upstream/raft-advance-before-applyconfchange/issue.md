Title: Calling Advance before applying a conf change, which Node.Advance allows, commits two different entries at one index

On `main` (1931ff5be, go1.26.9 linux/amd64), a leader whose application calls `Advance` before applying a `Ready`'s committed conf change, which `Node.Advance` allows, can accept a second conf change while the first is still unapplied; two nodes then commit different entries at one index. With voters 1, 2 and 3, node 1 leading, and node 1's application calling `Advance` before it applies a `Ready`'s committed entries:

1. Node 1 commits "remove 2" at index 2. Node 1's application calls `Advance` but not yet `ApplyConfChange`; nodes 2 and 3 apply "remove 2".
2. Node 1 accepts "remove 1" and commits it at index 3, still with voters 1, 2 and 3. Nodes 2 and 3 apply "remove 1", leaving node 3 the only voter in their configuration.
3. With node 3 cut off, node 1 commits `x` at index 4 with node 2.
4. Node 3 becomes leader on its own and commits its empty entry at index 4.

Index 4 should not be committed with two different entries.

[`Node.Advance`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/node.go#L166-L177) lets the application call `Advance` while it is still applying the last `Ready`, and [doc.go's step 4](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/doc.go#L101-L103) allows it "at any time after step 1". `Advance` moves raft's applied index whether or not `ApplyConfChange` has been called. Raft's checks for a pending conf change, [before accepting a conf change proposal](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1326) and [before campaigning](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L995-L998), treat every conf change up to the applied index as applied. In step 2, "remove 2" is at node 1's applied index but not applied, so node 1 accepts "remove 1" while its configuration still has voters 1, 2 and 3; node 1 then commits with a quorum of those voters, and node 3 alone, as the only voter of its configuration. This affects any application that calls `Advance` before `ApplyConfChange` and makes two membership changes in a row.

Unit test: [`TestNodeAdvanceBeforeApplyConfChange`](https://github.com/upamanyus/etcd-raft/blob/repro/raft-advance-before-applyconfchange/node_test.go#L1063-L1150) on branch [`upamanyus/etcd-raft:repro/raft-advance-before-applyconfchange`](https://github.com/upamanyus/etcd-raft/tree/repro/raft-advance-before-applyconfchange), off `main` (1931ff5be), runs these steps through `Node`. On `main` it fails (output trimmed):

```
--- FAIL: TestNodeAdvanceBeforeApplyConfChange (1.03s)
        	Error:      	Not equal: 
        	            	expected: "1/4 EntryNormal \"x\""
        	            	actual  : "2/4 EntryNormal \"\""
        	Messages:   	index 4 committed on nodes 1 and 3
```

If node 1's application calls `ApplyConfChange` before `Advance`, node 1 does not commit `x`. Is that order required? If so, `Node.Advance` and doc.go should say so.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.
