Title: A follower can install a snapshot of a term above its current term, sent by a leader that stepped down while saving a Ready

### What happened?

In Raft, a member's log has no term above the member's current term. In a cluster of five members, with member 1 leading term 1 and members 4 and 5 behind its compacted raft log:

1. While member 1 is slow to save a Ready (a slow disk), member 1, still leader, makes a `MsgSnap` of term 1 for each of members 4 and 5.
2. Before that save returns, member 1 steps down to follow member 2 at term 2. Its next Ready carries both `MsgSnap`s.
3. Member 1 applies an entry of term 2, and only then builds the snapshot it sends member 5, from what it has applied: the `MsgSnap` is of term 1, but its snapshot has term 2.
4. Member 5, still at term 1, installs the snapshot: its log ends at term 2.

The test below feeds etcd's server member 1's Readys from a fake raft node and delivers the `MsgSnap` to member 5, a raft node (output trimmed):

```
    logger.go:146: 2026-10-23T16:11:20.718Z	INFO	5 became follower at term 1
    logger.go:146: 2026-10-23T16:11:20.721Z	INFO	5 [commit: 3, lastindex: 3, lastterm: 2] restored snapshot [index: 3, term: 2]
        	Error:      	"2" is not less than or equal to "1"
        	Messages:   	last log term of member 5, at term 1, after it installs the MsgSnap
--- FAIL: TestMergedSnapshotTerm (0.01s)
```

This affects any leader that steps down while saving a Ready carrying a `MsgSnap` and applies entries of a newer term before sending it.

### What did you expect to happen?

Member 5's log should not end at a term above 1: a `MsgSnap` of term 1 should carry a snapshot of term at most 1, as raft's own `MsgSnap`s do.

### How can we reproduce it (as minimally and precisely as possible)?

Unit test: [`TestMergedSnapshotTerm`](https://github.com/upamanyus/etcd/blob/fix/etcd-merged-snapshot-stale-term/server/etcdserver/server_test.go#L759-L884) on branch [`upamanyus/etcd:fix/etcd-merged-snapshot-stale-term`](https://github.com/upamanyus/etcd/tree/fix/etcd-merged-snapshot-stale-term), off `main` (3aaab3479). On `main` it fails as above in 20 of 20 runs.

### Anything else we need to know?

A consequence, with a snapshot two or more terms newer than the message: a leader of a term in between, still up, can hear member 5 acknowledge an index past that leader's log, and panics with `need non-empty snapshot` if it has no snapshot yet. I reproduced that panic with the raft library alone, from member 5's state and hand-built messages, not in a running cluster.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (3aaab3479), go1.27.3 linux/amd64; the reproduction is a unit test, run without binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Any: the test runs etcd's server with a fake raft node.

</details>
