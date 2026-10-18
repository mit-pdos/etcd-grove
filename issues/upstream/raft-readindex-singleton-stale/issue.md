Title: ReadIndex at a new single-voter leader can return a stale index

### What happened?

With `ReadOnlySafe`:

1. Nodes 1 and 2 are the voters; node 2 leads.
2. Node 2 proposes its own removal (index 2) and, before applying it, an entry `x` (index 3); both nodes append both, and node 2 commits them.
3. The message telling node 1 that index 3 is committed is lost. Node 1 applies the removal and becomes leader as the only voter.
4. Before committing an entry in its new term, node 1 answers a read index request at once with index 2, missing `x`.

The test below runs these steps (output trimmed):

```
--- FAIL: TestReadOnlyForNewSingleVoterLeader (0.00s)
        	Error:      	"2" is not greater than or equal to "3"
        	Messages:   	read index
```

This affects any application that serves linearizable reads through `ReadIndex` after a removal leaves a single voter.

### What did you expect to happen?

Node 1's read index should be at least 3, so that the read includes `x`, which was committed before the read was issued.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestReadOnlyForNewSingleVoterLeader`](https://github.com/upamanyus/etcd-raft/blob/fix/raft-readindex-singleton-stale/raft_test.go#L2154-L2188) on branch [`upamanyus/etcd-raft:fix/raft-readindex-singleton-stale`](https://github.com/upamanyus/etcd-raft/tree/fix/raft-readindex-singleton-stale), off `main` (638f42739). On `main` it fails as above.

### Anything else we need to know?

I found this while formally verifying etcd, working with AI tools. I reproduced the bug and reviewed this report myself.

### Raft version

<details>

`main` (638f42739), go1.26.9 linux/amd64.

</details>
