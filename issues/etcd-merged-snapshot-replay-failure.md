---
upstream: none
checked: 2026-11-20
links: []
blocks-proof: yes
---

# The etcd fork reports a current-term snapshot as failed during restart replay

**Impact:** A restarted leader can have a database at index 7 while its apply loop is replaying index 3. When a follower needs a snapshot, the fork calls `ReportSnapshot(SnapshotFailure)` even though the database is available and the leader term still matches. The follower must wait for another replication attempt.

**Reproduction:** At the etcd fork pin `d3feef9bc`, copy the test to `server/etcdserver/` and run the following from `server/`. The test persists index 7, its entry term 2, and a configuration with a learner. It reopens that database, places a term-3 snapshot request on the raft channel and runs the production apply loop. The transport captures the streamed database and checks its index, term and configuration against the raft label. On the pinned fork the transport receives no message. [Go test](etcd-merged-snapshot-replay-failure/merged_snapshot_replay_test.go)

```sh
go test ./etcdserver -run '^TestMergedSnapshotDuringReplay$' -count=1
```

The replay window also occurs in a five-member cluster with graceful restarts. Before the deferral was added, a follower received a snapshot labelled 217 whose database was already at 467. [Cluster reproduction](../nonissues/etcd-backward-snapshot-install-panics-watcher/inwindow_merge_test.go)

**Expected:** The follower receives a snapshot whose index, entry term and configuration describe the database it installs.

**Cause:** The sender compares its replay cursor with the consistent index. When the cursor is behind, the sender reports failure without opening the database snapshot.

## Fork repair

The replay branch reads the index, term and ConfState from the bbolt read transaction that streams the database. A legacy backend can lack the term or ConfState. For that format it takes the term from the immutable log suffix at the same Ready and the voters and learners from the frozen membership. The Go test reopens the database with a recovered WAL commit of 3 and verifies a delivered snapshot at index 7, entry term 2, in message term 3. It exercises both backend formats. A separate test replaces part of a log suffix and checks that an earlier batch still sees its original terms. The test constructs the post-crash disk state directly. [Fork regression tests](https://github.com/upamanyus/etcd/blob/03c73a97acffff218b6cb19f91b2586e7321317b/server/etcdserver/merged_snapshot_replay_test.go)

## Proof

The fork introduced the deferral in `6e8f0c004`. The sender proof uses that branch to exclude the case where the committed database is ahead of the replay cursor. After a machine crash the durable database can also be ahead of the recovered HardState commit. The regression test sets up the sender's replay window directly and does not simulate such a crash. [Crash and replay analysis](../nonissues/etcd-backward-snapshot-install-panics-watcher.md)
