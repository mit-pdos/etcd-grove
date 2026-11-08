---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/etcd#18055 issue open: related, not this: the raft loop's Release deletes a received snapshot's .snap.db before the apply loop opens it (issues/etcd-release-snapdb-before-open.md); the purge is a second remover of the same files
blocks-proof: yes
---

# etcdserver: the snapshot-database purge deletes a received snapshot's `.snap.db` that the apply loop has not opened yet

`EtcdServer.purgeFile` runs `fileutil.PurgeFileWithoutFlock` on the snapshot directory every 30
seconds (and once at `Start`), keeping the newest `maxSnapDBFiles = 5` `.snap.db` files (a constant,
not `--max-snapshots`) and deleting the older ones by name, without a lock and without asking the
apply loop. When six or more `.snap.db` files are present and the oldest is a snapshot raft has
handed to the apply loop but `applySnapshot` has not opened yet, the purge deletes it and
`applySnapshot` panics ("failed to open snapshot backend": `snap: snapshot file doesn't exist`).

**Why not an issue:** no test reaches it the way etcd runs: the test stages the six files directly
(as rafthttp's snapshot handler saves them) and drives `raftNode` with the package's fake raft
node. In a running cluster a follower does not hold five received snapshots newer than one it has
not opened: the raft loop blocks on a received snapshot's second `notifyc` send until the apply
loop has taken its first (`raft.go`, the follower branch), so it hands out at most one snapshot
beyond the one `applySnapshot` is opening, and it sends none of its responses meanwhile, so the
leader does not send it another `MsgSnap` (the leader's probe after a snapshot waits for a
heartbeat response, raft `MsgSnapStatus`/`MsgHeartbeatResp`). The other files the purge counts are
orphans: `MsgSnap`s rafthttp saved but raft ignored (a stale term, an index at or below the commit
index) or files left by a crash between `SaveDBFrom` and the raft loop's persistence; reaching five
of them above a pending snapshot takes leader changes, partitions or crashes in an order not
excluded by any check but not shown possible either. The purge is etcd's intent for orphans;
the hazard is that it does not distinguish them from a pending snapshot.

## Proof

yes: the proof rests on `EtcdServer.purgeFile`'s trust-boundary triple, whose post is `True` and
which touches no resource, while the snapshot directory's invariant (`snapDirInv`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Net.lean`) keeps each saved `.snap.db`
(`backend.fileHolds`) until its removal fact `srvSnapRm` (opened at or above, or applied past) holds,
and `applySnapshot`'s open is proved not to fail from it (`snapDir_take`, `SnapRO.lean`, with the
premise `storage.snapOpensOk`): the triple is false for the directory the purge shares
(`TestPurgeFileRemovesUnopenedSnapDB` is the direct counterexample). A repair needs either a fork
change (the purge skips, or no longer runs on, `.snap.db` files above the last opened snapshot,
since `applySnapshot`'s own `Release` removes those below it) or a proved bound on the files above a
pending snapshot, which the proof does not have.

**Fixed on the fork** (sweep repairs 1, R1-3, 2026-11-08; the user's option A via etcd-grove-82):
upamanyus/etcd@a4d2bb172 (`goose-lean`, the pin of `etc/goose.py`'s `etcd` project) no longer
purges `.snap.db` files in `purgeFile`; `Snapshotter.ReleaseSnapDBs`, which `storage.Release` calls
after a received snapshot is opened and after a snapshot is taken, removes the ones below it. So
`purgeFile` no longer touches the snapshot directory, and `snapDirInv` is again true next to it. The
bug still blocks the proof in this file's sense: the proof needs the fork's fix.

## Notes

Regression tests (the fork's, `server/etcdserver/purge_snapdb_test.go` at a4d2bb172, copied as
[`purge_snapdb_regression_test.go`](etcd-purge-snapdb-unopened/purge_snapdb_regression_test.go)):
`TestPurgeFileKeepsSnapDBs` and `TestPurgeSnapDBBeforeApply` fail at 673da07c8 and pass at a4d2bb172
(5 of 5 runs each, `go test ./etcdserver -run ... -count=5`, 2026-11-08).


Tests: [`nonissues/etcd-purge-snapdb-unopened/purge_snapdb_test.go`](etcd-purge-snapdb-unopened/purge_snapdb_test.go),
copied (as `zz_purge_snapdb_test.go`) into `server/etcdserver` at the verified fork's pin
upamanyus/etcd@673da07c8fab (`goose-lean`, which carries the fix of
`issues/etcd-release-snapdb-before-open.md`), go1.27.3 linux/amd64; it reuses `newNopReadyNode`
and `newNopTransporter` of `server_test.go`. `TestPurgeSnapDBBeforeApply` runs the scenario in a
child process (the panic is on the apply goroutine): six `.snap.db` files (indexes 2..12), raft hands
out snapshot 2, the apply loop is held before its open by `bemu` (as a long `Defragment`, which holds
`bemu.RLock` for the whole call, would), the purge goroutine runs one pass, the hold is released.
20 of 20 runs of each test fail; with five files (a control) 10 of 10 pass:

```
$ (cd server && go test ./etcdserver -run '^(TestPurgeFileRemovesUnopenedSnapDB|TestPurgeSnapDBBeforeApply)$' -count=20)
--- FAIL: TestPurgeFileRemovesUnopenedSnapDB (0.04s)
    zz_purge_snapdb_test.go:82: snapshot 2's database file was purged before it was opened: snap: snapshot file doesn't exist
--- FAIL: TestPurgeSnapDBBeforeApply (0.16s)
    zz_purge_snapdb_test.go:111: the apply loop panicked: the purge removed the pending snapshot's .snap.db:
        panic: failed to open snapshot backend [recovered]
```

Upstream `main` has the same purge; there the raft loop's `Release` (#18055) removes these files
first. GitHub was not searched for this finding from this session (no `gh`).
