Title: A new leader of a single-voter configuration answers ReadIndex with a stale index

### What happened?

Of two voters 1 and 2, leader 2 removes itself (index 2) and commits `x` (index 3), and node 1 learns only that index 2 is committed. Node 1 becomes leader of the configuration `{1}` and, with `ReadOnlySafe`, answers a read index request at once with index 2, which misses `x` (output trimmed):

```
--- FAIL: TestReadOnlyForNewSingleVoterLeader (0.00s)
        	Error:      	Not equal: 
        	            	expected: []raft.ReadState{raft.ReadState{Index:0x4, RequestCtx:[]uint8{0x63, 0x74, 0x78}}}
        	            	actual  : []raft.ReadState{raft.ReadState{Index:0x2, RequestCtx:[]uint8{0x63, 0x74, 0x78}}}
```

This affects any application serving linearizable reads through `ReadIndex` whose configuration a removal reduced to one voter that missed the previous leader's last commit index.

### What did you expect to happen?

Node 1 answers the read only after it commits an entry at its term (index 4), as a new leader with more voters does (`TestReadOnlyForNewLeader`).

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestReadOnlyForNewSingleVoterLeader`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-readindex-singleton-stale/raft_test.go) on branch [`upamanyus/etcd-raft:fix/raft-readindex-singleton-stale`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-readindex-singleton-stale), off `main` (638f42739). On `main` it fails as above.

### Anything else we need to know?

In the same start, if leader 2 applies its removal and is then partitioned from node 1 (with `StepDownOnRemoval` unset), node 2 still answers read index requests at once with index 2 after node 1 has been elected in a later term and committed a new entry at index 4 (reproduced with a test that is not on the branch). Setting `StepDownOnRemoval` avoids this case only.

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
