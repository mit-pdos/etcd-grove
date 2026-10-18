Title: A leader that removed itself answers ReadIndex with a stale index

### What happened?

With `ReadOnlySafe` and `StepDownOnRemoval` unset:

1. Nodes 1 and 2 are the voters; node 2 leads.
2. Node 2 removes itself, and both nodes apply the removal. Node 2 stays leader.
3. Node 1, now the only voter, becomes leader and commits an entry `y` (index 4).
4. Node 2 answers a read index request at once with index 2, missing `y`.

The test below runs these steps (output trimmed):

```
--- FAIL: TestReadOnlyForRemovedLeader (0.00s)
        	Error:      	"2" is not greater than or equal to "4"
        	Messages:   	read index
```

This affects any application that serves linearizable reads through `ReadIndex`, with `StepDownOnRemoval` unset, at a leader that removed itself.

### What did you expect to happen?

Node 2 should not answer the read with an index below 4: a read issued after `y` was committed should include `y`.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestReadOnlyForRemovedLeader`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-readindex-removed-leader/raft_test.go#L2227-L2260) on branch [`upamanyus/etcd-raft:fix/raft-readindex-removed-leader`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-readindex-removed-leader), off `main` (638f42739). On `main` it fails as above.

### Anything else we need to know?

Setting `StepDownOnRemoval` avoids this.

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
