---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22516 issue open: this bug (by gyuho: a member that catches up from a snapshot rejects proposals with "too many requests", its publish included)
  - etcd-io/etcd#22510 pr open: the fix (`setAppliedIndex` after `applySnapshot`), by gyuho
  - etcd-io/etcd#22528 issue open: this bug again (a new joiner stuck on "too many requests" in an idle cluster; marked a duplicate of #22516 in its comments)
  - etcd-io/etcd#22524 issue open: related (a member caught up from a snapshot becomes ready only after its first publish times out)
blocks-proof: no
---

# etcdserver: after a member installs a leader's snapshot it refuses every write with "too many requests" until another write commits

After a follower catches up by a leader's snapshot, the applied index it uses to limit proposals
stays at its old value, so in a quiet cluster every write through it fails with `etcdserver: too
many requests` until some other member's write commits. Default configuration
(`SnapshotCatchUpEntries` 5000, the same as the limit).

**Reproduction:** `TestAppliedIndexStaleAfterSnapshotInstall` in
[`issues/etcd-applied-index-stale-after-snapshot/applied_index_after_snapshot_test.go`](etcd-applied-index-stale-after-snapshot/applied_index_after_snapshot_test.go),
copied into `tests/integration` at etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef
(2026-10-28), go1.27.3 linux/amd64:

```
$ go test ./integration -run TestAppliedIndexStaleAfterSnapshotInstall -count=1
        	Error Trace:	.../tests/integration/zz_applied_snap_test.go:56
        	Error:      	Received unexpected error:
        	            	rpc error: code = Unknown desc = etcdserver: too many requests
        	Messages:   	put 0 through the follower after its snapshot install (applied 8, committed 5208)
--- FAIL: TestAppliedIndexStaleAfterSnapshotInstall (11.74s)
FAIL	go.etcd.io/etcd/tests/v3/integration	13.135s
```

**Cause:** [`applySnapshot`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L1140-L1141)
moves the apply loop's progress to the snapshot's index but never calls `setAppliedIndex` (only
[`applyEntries`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L1914-L1923)
does), while the committed index moves to the snapshot's; every proposal is refused while
committed exceeds applied by more than 5000
([`processInternalRaftRequestOnce`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/v3_server.go#L1060-L1066)).

## Proof

no: the verified code keeps Go's behavior; the server's invariant relates the atomic applied index
to the applied log by "at most" rather than equality (D22 J5,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean`), and request-limit refusals are
liveness only.

## Notes

The `Status` fields `RaftAppliedIndex` and `RaftTerm` are stale over the same window. Found
2026-10-26, three weeks after upstream's #22516 (2026-10-03); the test here is independent of
#22510's.
