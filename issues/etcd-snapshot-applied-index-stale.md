---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22528 issue open: same bug (a joiner in an idle cluster stuck in "too many requests"), the report this was triaged from
  - etcd-io/etcd#22516 issue open: same bug (member stays unpublished after catching up from a snapshot)
  - etcd-io/etcd#22510 pr open: the fix (setAppliedIndex/setTerm at the end of applySnapshot), with a unit test
  - etcd-io/etcd#22529 pr open: the same fix
  - etcd-io/etcd#22526 issue open: related (publishV3 retries "too many requests" in a tight loop)
  - etcd-io/etcd#22527 pr open: related (publishV3 waits for apply before retrying)
---

# Applying a leader snapshot leaves the server's applied index behind

- **Status**: a bug. A member that catches up purely from a leader snapshot keeps
  `s.appliedIndex` at its pre-snapshot value while `s.committedIndex` jumps to the snapshot's index.
  If the gap exceeds 5000 and no entry follows (an idle cluster), every proposal is refused with
  `ErrTooManyRequests` indefinitely, including the member's own `publishV3`. The member never
  becomes ready.
- **Where**: at the etcd pin of `etc/goose.py` (`107edf7e4`; same on upstream `main`):
  `EtcdServer.applySnapshot` (`server/etcdserver/server.go:1001`) sets `ep.appliedi`/`ep.appliedt`
  to the snapshot's (`:1140-1141`) but does not call `s.setAppliedIndex` (`:1684`), whose only
  callers are in `EtcdServer.apply` (`:1914`, `:1922`). `updateCommittedIndex`
  (`server/etcdserver/raft.go:344`) raises the committed index to the snapshot's.
  `processInternalRaftRequestOnce` (`server/etcdserver/v3_server.go:1059`) refuses via
  `exceedsRequestLimit` (`server/etcdserver/util.go:60`, gap `> maxGapBetweenApplyAndCommitIndex =
  5000`). The retry loop is `publishV3` (`server.go:1793`). The bug has been there since at least
  v3.4.
- **What happens**: reproduced at the pin by
  `issues/etcd-snapshot-applied-index-stale/snapshot_applied_index_test.go` (package
  `etcdserver`, adapted from PR #22510's test; passes at the pin). A `Ready` carrying a snapshot at
  index 10001 is applied, and `ApplyWait(10001)` fires. Then:

  ```go
  require.Equal(t, snapIndex, s.CommittedIndex())   // 10001
  require.Equal(t, uint64(0), s.AppliedIndex())     // still 0
  _, err = s.Put(ctx, &pb.PutRequest{Key: []byte("foo"), Value: []byte("bar")})
  require.ErrorIs(t, err, errors.ErrTooManyRequests) // never reaches raft
  ```

  End to end: the scripts in #22528 (a 3-member cluster past `snapshot-count`, idle, `member add`
  with an empty data dir) leave the new member logging "failed to publish ... too many requests"
  until any write is made through another member, or the member is restarted.
- **Expected**: after a snapshot is applied, the applied index (and term) is the snapshot's, as
  `ep.appliedi` already is, and proposals are admitted.
- **How the proof handles it**: outside the verified scope by a premise. The apply thread's specs
  are proved only for batches without a snapshot: `EtcdServer.applyAll.spec` and
  `EtcdServer.applySnapshot.spec` require `taSnapshotAddr ap ↦□ null`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean:51`,
  `EtcdServer__applySnapshot.lean:31`), carried from the raft loop's `rnApP`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRaftNode.lean:679-683`). Once that premise is
  dropped (`server-apply-snapshot`), the existing invariant excludes the bug, provided `applyAll`'s
  postcondition keeps the shape `epAppliedIAddr ep ↦ ai' ∗ srvAppliedOwn γr ai'` (`:64`).
  `srvAppliedOwn` and `srvAppliedInv` (`InvRequest.lean:1800-1816`) tie the atomic
  `s.appliedIndex` to the ghost applied index. The hang itself (publish never succeeds) is
  liveness, and `publishV3` is an axiom (`Proof/.../EtcdServer__publishV3.lean:24`).
- **Possible fixes**: call `s.setAppliedIndex(ep.appliedi)` and `s.setTerm(ep.appliedt)` at the
  end of `applySnapshot` (#22510, #22529). Independently, back off in `publishV3` on
  `ErrTooManyRequests` (#22527).
- **Found**: 2026-10-16, by the bug triage of etcd-io/etcd#22528
  (`notes/bug-triage/etcd-22528.md`).
