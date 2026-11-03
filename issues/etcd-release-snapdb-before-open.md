---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#18055 issue open: this bug (robustness test; root cause by ahrtr, "lock the snapshot file until it has been applied")
  - etcd-io/etcd#20133 issue closed: duplicate (Antithesis, main 3be967f, default configuration)
  - etcd-io/etcd#20657 issue closed: duplicate (3.5.18, two snapshots at index 17 and 18)
  - etcd-io/etcd#21082 pr closed: an earlier fix attempt, unmerged
  - etcd-io/etcd#22046 pr open: keep snapshot db files until they have been applied, with a test
blocks-proof: yes
---

# etcdserver: a follower that receives two snapshots in quick succession panics with "failed to open snapshot backend"

When raft hands a follower a second snapshot before its apply loop has opened the first one's
`.snap.db` file, the raft goroutine's `Release` of the second snapshot deletes the first one's file,
and the apply loop panics opening it (`failed to open snapshot backend`). The member recovers on
restart.

**Reproduction:** `TestSnapshotDBKeptUntilOpened` in
[`issues/etcd-release-snapdb-before-open/snapshot_db_kept_test.go`](etcd-release-snapdb-before-open/snapshot_db_kept_test.go),
copied (as `zz_snapshot_db_kept_test.go`) into `server/etcdserver` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3; it drives `raftNode`
with the package's fake raft node (snapshots 2 and 4) while holding `bemu`, so the apply loop's
`applySnapshot(2)` waits before its open, as a slow apply goroutine would:

```
$ (cd server && go test ./etcdserver -run '^TestSnapshotDBKeptUntilOpened$' -count=1)
--- FAIL: TestSnapshotDBKeptUntilOpened (0.26s)
    zz_snapshot_db_kept_test.go:154: expected file "/tmp/TestSnapshotDBKeptUntilOpened2294783365/002/member/snap/0000000000000002.snap.db", got missing: released before applySnapshot opened it
FAIL
```

## Proof

yes: the verified fork carries a fix (`goose-lean` `188113160`: `applySnapshot` releases the older
files itself, after it has opened its snapshot's backend); the snapshot directory's removal fact
needs it (`notes/decisions.md`, "D22 S-j2 carried out").

## Notes

#22046 is the same idea (keep the files until applied); supporting it is the useful step, not a new
report.
