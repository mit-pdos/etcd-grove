Title: A restarted member panics on a leader transfer to it while it applies the entries replayed from its WAL

### What happened?

In a 3-member cluster with default settings:

1. The cluster takes 150 puts. A follower `m0` is stopped and restarted; it has no snapshot on disk yet, so it replays all 158 committed entries from its WAL.
2. While `m0` applies the replayed entries, the leader `m2` transfers its leadership to `m0` (`MoveLeader`).
3. `m0` panics on receiving the transfer:

```
INFO	m2.raft	7aee498246d61f31 sends MsgTimeoutNow to 955c5cff599ee2d5 immediately as 955c5cff599ee2d5 already has up-to-date log
INFO	m0.raft	955c5cff599ee2d5 [term 2] received MsgTimeoutNow from 7aee498246d61f31 and starts an election to get leadership.
PANIC	m0.raft	error scanning unapplied entries [1, 159): requested index is unavailable due to compaction
panic: error scanning unapplied entries [1, 159): requested index is unavailable due to compaction
...
go.etcd.io/raft/v3.(*raft).hasUnappliedConfChanges(0x2979a1592300)
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:1018 +0x1cc
go.etcd.io/raft/v3.(*raft).hup(0x2979a1592300, {0x10138c3, 0x10})
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:983 +0x105
go.etcd.io/raft/v3.stepFollower(0x2979a1592300, 0x2979a0c23c70)
	/home/ubuntu/go/pkg/mod/go.etcd.io/raft/v3@v3.7.0/raft.go:1763 +0x5df
...
FAIL	go.etcd.io/etcd/tests/v3/integration	0.780s
```

The window is short: from when the member finishes applying a batch of entries until its raft node moves on to the next batch.

### What did you expect to happen?

`m0` should not crash: it should take the leadership or refuse the transfer, and keep serving requests.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestMoveLeaderToRestartedMember`](https://github.com/upamanyus/etcd/blob/fix/etcd-compact-past-raft-applied/tests/integration/v3_leadership_test.go#L185-L222) on branch [`upamanyus/etcd:fix/etcd-compact-past-raft-applied`](https://github.com/upamanyus/etcd/tree/fix/etcd-compact-past-raft-applied), off `main` (7ff040cb8). It needs failpoints (`make gofail-enable`, or `gofail enable server/etcdserver/`), and uses `raftBeforeFollowerSend` with `sleep("2s")` to hold each follower after it has applied a batch. On `main` it fails with the panic above.

### Anything else we need to know?

Without the failpoint, I did not measure how often a transfer lands in the window.

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (7ff040cb8), go1.27.2 linux/amd64, gofail v0.2.0; integration cluster, no binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Defaults of the integration test cluster, 3 members.

</details>
