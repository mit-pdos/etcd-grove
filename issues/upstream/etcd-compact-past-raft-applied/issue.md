Title: A restarted member panics on a leader transfer to it while it applies the entries replayed from its WAL

### What happened?

In a 3-member cluster with default settings:

1. The cluster commits 150 puts. A follower `m2` is stopped and restarted; it has no snapshot on disk yet, so it replays all 158 committed entries from its WAL.
2. While `m2` applies the replayed entries, the leader `m1` transfers its leadership to `m2` (`MoveLeader`).
3. `m2` panics on receiving the transfer:

```
INFO	m1.raft	5cf030eae9de3f3d sends MsgTimeoutNow to 93ff37bd058fd040 immediately as 93ff37bd058fd040 already has up-to-date log
INFO	m2.raft	93ff37bd058fd040 [term 2] received MsgTimeoutNow from 5cf030eae9de3f3d and starts an election to get leadership.
PANIC	m2.raft	error scanning unapplied entries [1, 159): requested index is unavailable due to compaction
panic: error scanning unapplied entries [1, 159): requested index is unavailable due to compaction
...
go.etcd.io/raft/v3.(*raft).hasUnappliedConfChanges(0x3feaf804e300)
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:1018 +0x1cc
go.etcd.io/raft/v3.(*raft).hup(0x3feaf804e300, {0x10148ca, 0x10})
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:983 +0x105
go.etcd.io/raft/v3.stepFollower(0x3feaf804e300, 0x3feaf9657450)
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:1763 +0x5df
...
```

The window is short: from when the member finishes applying a batch of entries until its raft node moves on to the next batch.

### What did you expect to happen?

`m2` should not crash: it should take the leadership or refuse the transfer, and keep serving requests.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestMoveLeaderToRestartedMember`](https://github.com/upamanyus/etcd/blob/fix/etcd-compact-past-raft-applied/tests/integration/v3_leadership_test.go#L185-L222) on branch [`upamanyus/etcd:fix/etcd-compact-past-raft-applied`](https://github.com/upamanyus/etcd/tree/fix/etcd-compact-past-raft-applied), off `main` (3aaab3479). It needs failpoints (`make gofail-enable`); `raftBeforeFollowerSend` with `sleep("2s")` widens the window. On `main` it panics as above in 3 of 3 runs.

### Anything else we need to know?

Only `m2` crashes, and a restart clears it: started again alone on its data directory, `m2` replayed all 158 entries (all 150 puts) without error and campaigned without panicking. From reading the code, every restart of a member with no snapshot on disk and more than 100 entries to replay reopens the window (not reproduced). Without the failpoint, I did not measure how often a transfer or an election lands in the window.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (3aaab3479), go1.27.3 linux/amd64, gofail v0.2.0; the integration test, and `etcd` built from `main` with `go build` to restart the member's data directory.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Defaults of the integration test cluster, 3 members.

</details>
