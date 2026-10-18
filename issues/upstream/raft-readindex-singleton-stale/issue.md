Title: A new leader of a single-voter configuration answers ReadIndex with a stale index

### What happened?

With `ReadOnlySafe`, a read index can miss a committed entry once a removal leaves a single voter:

1. Nodes 1 and 2 are the voters; node 2 leads.
2. Node 2 commits its own removal (index 2), then an entry `x` (index 3).
3. Node 1 learns that index 2 is committed, but not index 3, and becomes leader as the only voter.
4. Node 1 answers a read index request at once with index 2, which misses `x`.

The test below runs these steps (output trimmed):

```
--- FAIL: TestReadOnlyForNewSingleVoterLeader (0.00s)
        	Error:      	Not equal: 
        	            	expected: []raft.ReadState{raft.ReadState{Index:0x4, RequestCtx:[]uint8{0x63, 0x74, 0x78}}}
        	            	actual  : []raft.ReadState{raft.ReadState{Index:0x2, RequestCtx:[]uint8{0x63, 0x74, 0x78}}}
```

This affects any application that serves linearizable reads through `ReadIndex` after a removal leaves a single voter.

### What did you expect to happen?

Node 1 answers only after committing an entry in its own term, as a new leader with more voters does (`TestReadOnlyForNewLeader`): read index 4, which includes `x`.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestReadOnlyForNewSingleVoterLeader`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-readindex-singleton-stale/raft_test.go) on branch [`upamanyus/etcd-raft:fix/raft-readindex-singleton-stale`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-readindex-singleton-stale), off `main` (638f42739). On `main` it fails as above.

### Anything else we need to know?

A leader that removed itself has the same problem: unless `StepDownOnRemoval` is set, node 2 stays leader after its removal, and if partitioned from node 1 it keeps answering at once with index 2 after node 1 has committed newer entries (reproduced with a test not on the branch). `StepDownOnRemoval` avoids only this second case.

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
