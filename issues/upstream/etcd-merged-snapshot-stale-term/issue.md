Title: A leader that steps down while saving a Ready can send a MsgSnap whose snapshot is newer than the message's term

### What happened?

In a cluster of five members, with member 1 leading term 1 and members 4 and 5 behind its compacted raft log:

1. While member 1 is slow to save a Ready (a slow disk), member 1, still leader of term 1, makes a `MsgSnap` of term 1 for each of members 4 and 5.
2. Before that save returns, member 1 steps down to follow member 2 at term 2. Its next Ready still carries both `MsgSnap`s.
3. Member 1 applies an entry of term 2, then sends member 5 a `MsgSnap` of term 1 whose snapshot has term 2.

The test below feeds etcd's server member 1's Readys from a fake raft node (output trimmed):

```
--- FAIL: TestMergedSnapshotTerm (0.01s)
        	Error:      	"2" is not less than or equal to "1"
        	Messages:   	snapshot term of the MsgSnap to 5
```

This affects any leader that steps down while saving a Ready that carries a `MsgSnap` and applies entries of a newer term before sending it.

### What did you expect to happen?

A `MsgSnap` of term 1 should carry a snapshot of term at most 1, as the `MsgSnap`s raft makes do.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestMergedSnapshotTerm`](https://github.com/upamanyus/etcd/blob/fix/etcd-merged-snapshot-stale-term/server/etcdserver/server_test.go#L759-L855) on branch [`upamanyus/etcd:fix/etcd-merged-snapshot-stale-term`](https://github.com/upamanyus/etcd/tree/fix/etcd-merged-snapshot-stale-term), off `main` (6782f5229). On `main` it fails as above, in 20 runs of 20.

### Anything else we need to know?

Member 5, still at term 1, installs this snapshot, so its last log term is above its current term. With a snapshot two or more terms newer than the message, a leader of a term in between, still up, can then hear member 5 acknowledge an index past that leader's log, and that leader panics with `need non-empty snapshot` if it has no snapshot yet. I reproduced that panic with the raft library alone, from member 5's state and hand-built messages, not in a running cluster.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (6782f5229), go1.27.2 linux/amd64; the reproduction is a unit test, run without binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Any: the test runs etcd's server with a fake raft node.

</details>
