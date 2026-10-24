---
upstream: none
checked: 2026-10-23
links:
candidate: issues/upstream/raft-snapshot-during-apply-stale-confchange/
---

# raft: a snapshot restored while a `Ready`'s conf changes are being applied makes `ApplyConfChange` apply them on top of the snapshot's configuration

- **Status**: open (not reported upstream). Reproduced on raft by Go tests with hand-built
  leader messages; not demonstrated in a full cluster or on etcd. On etcd-io/raft `main`
  638f42739 also with a real leader `raft` (a temporary test, 2026-10-18,
  `issues/upstream/raft-snapshot-during-apply-stale-confchange/meta.md`, which also records why the
  candidate's earlier fixes were replaced: ignoring the snapshot made the leader's resend depend on
  `ReportSnapshot`; deferring it (2026-10-18) can make the leader send it twice, measured 2026-10-21). Since 2026-10-23 the candidate
  does not deal with `AsyncStorageWrites` (its fix and test are for the synchronous mode; the changelog commit was
  dropped that day too): with it, the fix also needs
  [raft-async-snapshot-during-apply-divergence](raft-async-snapshot-during-apply-divergence.md)'s hold, a
  candidate of its own; the two merge cleanly and together fix the async case.
- **Where** (etcd-io/raft at `40f8be730b18`):
  - `node.go:380-445` (`node.run`): while it waits for `Advance` (`advancec != nil`) it still
    steps the messages it receives (`case m := <-n.recvc: r.Step(m)`); `doc.go:110` ("when
    you receive a message from another node, pass it to Node.Step") puts no condition on it.
    With `RawNode`, nothing forbids `Step` between `Ready` and `Advance` either
    (`rawnode.go:402-404` only forbids changes between `Ready` and `acceptReady`).
  - `raft.go:1849-1856` (`restore`): a snapshot past the commit index is restored, and the
    configuration replaced by its `ConfState` (`raft.go:1904-1924`), whether or not committed
    entries handed out in the last `Ready` (`raftLog.applying`) are still being applied.
  - `raft.go:1939-1958` (`applyConfChange`) applies the change it is given to the
    configuration in use; it has no index to tell that the change is older than that
    configuration.
- **What happens**: a follower receives `C1` committed in a `Ready` and starts applying it
  (`doc.go` step 3). Meanwhile the leader, whose log is compacted past the follower's
  progress, sends a snapshot at a later index; the follower restores it, so its
  configuration is the snapshot's, which already reflects `C1` and later changes. The
  application then finishes applying `C1` and calls `ApplyConfChange(C1)`: the change is
  applied a second time, on top of the snapshot's configuration. The next `Ready` carries
  the snapshot, but raft does not re-install its `ConfState`; the node keeps a configuration
  that is no prefix's of the log until it restarts.
  Reproduction (`raft-conf-lag-model/snapshot_during_apply_test.go`, public `RawNode` API,
  the application faithful: `ApplyConfChange` before `Advance`):

      cp issues/raft-conf-lag-model/snapshot_during_apply_test.go <etcd-raft checkout>/
      cd <etcd-raft checkout> && go test -run TestSnapshotDuringApply -v .
      ...
      snapshot_during_apply_test.go:99: DIVERGENCE reproduced: node 2 uses voters=(1 2 3 4), the log's configuration at index 3 is voters=(1 2 3)
      ...
      snapshot_during_apply_test.go:147: PANIC reproduced: config is already joint

  `TestSnapshotDuringApplyStaleConfChange`: `C1 = add 4` (index 1), snapshot at index 3 with
  `{1,2,3}` (after a `remove 4` at index 2): node 2 ends at `voters=(1 2 3 4)`.
  `TestSnapshotDuringApplyStaleEnterJointPanics`: `C1` enters a joint configuration, the
  snapshot (index 2) was taken in it; `ApplyConfChange(C1)` panics in
  `applyConfChange` ("config is already joint"). The leader's messages are built by hand
  (a `MsgApp` committing index 1, then a `MsgSnap` at index 2 or 3), each of a kind a leader
  sends; in a cluster the snapshot needs a follower behind the leader's compaction point
  while it is still applying an older batch.
- **How it happens**: nothing stops a node from stepping messages between `Ready` and
  `Advance`; `node.run` does it itself. A `MsgSnap` past the commit index is restored, and
  `restore` replaces the configuration with the snapshot's `ConfState` without looking at the
  committed entries the last `Ready` handed out. `applyConfChange` later receives only the
  change, with no index, and applies it to the configuration in use. The execution of
  `TestSnapshotDuringApplyStaleConfChange`:
  1. `C0 = {1,2,3}`. Follower 2 receives `C1 = add 4` at index 1, committed. Its `Ready` hands
     out `C1`, and the application starts applying it.
  2. The leader commits `C2 = remove 4` at index 2 and something at index 3, compacts, and
     sends node 2 a snapshot at index 3 with `ConfState {1,2,3}`. That configuration already
     reflects `C1` and `C2`.
  3. Node 2 steps the `MsgSnap`. Index 3 is above its commit index 1, so it restores:
     configuration `{1,2,3}`.
  4. The application finishes `C1` and calls `ApplyConfChange(C1)`, then `Advance`. raft
     applies `add 4` on top of the snapshot's configuration: `{1,2,3,4}`.
  5. The next `Ready` carries the snapshot, and the application applies it, but raft does not
     re-install its `ConfState`. Node 2 stays on `{1,2,3,4}`, while the log's configuration at
     index 3 is `{1,2,3}`.

  ```go
  // node.go:394-399, 435-445 (etcd-io/raft 40f8be7), node.run
  		case m := <-n.recvc:
  			if IsResponseMsg(m.Type) && !IsLocalMsgTarget(m.From) && r.trk.Progress[m.From] == nil {
  				// Filter out response message from unknown From.
  				break
  			}
  			r.Step(m) // <- also while the application holds a Ready
  		// ...
  		case readyc <- rd:
  			n.rn.acceptReady(rd)
  			if !n.rn.asyncStorageWrites {
  				advancec = n.advancec
  			} else {
  				rd = Ready{}
  			}
  			readyc = nil // <-
  		case <-advancec:
  			n.rn.Advance(rd)
  			rd = Ready{}
  ```

  ```go
  // raft.go:1849-1852, 1909-1924, 1939-1959 (etcd-io/raft 40f8be7)
  func (r *raft) restore(s pb.Snapshot) bool {
  	if s.Metadata.Index <= r.raftLog.committed {
  		return false
  	}
  	// ... (the snapshot is not in the log)
  	r.raftLog.restore(s)

  	// Reset the configuration and add the (potentially updated) peers in anew.
  	r.trk = tracker.MakeProgressTracker(r.trk.MaxInflight, r.trk.MaxInflightBytes) // <-
  	cfg, trk, err := confchange.Restore(confchange.Changer{
  		Tracker:   r.trk,
  		LastIndex: r.raftLog.lastIndex(),
  	// ...
  	assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk)) // <-
  // applyConfChange has no index: it applies cc to whatever r.trk is now
  func (r *raft) applyConfChange(cc pb.ConfChangeV2) pb.ConfState {
  	cfg, trk, err := func() (tracker.Config, tracker.ProgressMap, error) {
  		changer := confchange.Changer{
  			Tracker:   r.trk, // <-
  			LastIndex: r.raftLog.lastIndex(),
  		}
  	// ...
  	return r.switchToConfig(cfg, trk)
  }
  ```
- **Consequences**: a wrong configuration on a follower is used for its vote tally if it
  campaigns and for its commit quorum if it wins. One stale single change keeps majorities
  intersecting (adjacent configurations); several in one `Ready`, or a stale removal of a
  node re-added later, need not. With joint consensus the stale `EnterJoint` is a panic,
  which recurs if the same interleaving recurs.
- **etcd**: plausibly exposed, not demonstrated. etcd's raft loop (`etcdserver/raft.go:185-336`)
  hands a follower's committed entries to the apply goroutine and, when they contain a conf
  change, waits for it before `Advance`; meanwhile `node.run` keeps stepping messages from
  the transport, `MsgSnap` included. The leader snapshots a follower that is more than
  `SnapshotCatchUpEntries` (5000) entries behind its compaction point. etcd's membership
  store is then right (it restores the snapshot) while raft's configuration is not.
- **Expected**: either raft ignores `ApplyConfChange` calls for conf changes that a restored
  snapshot supersedes, or the documentation forbids stepping messages (or at least
  `MsgSnap`) while a `Ready`'s committed entries are being applied, which `node.run`
  itself violates.
- **How the proof handles it**: not reached; the verified scope never applies a conf change
  (`HnoConfChange` in `ownRaftLog`), and the reconfiguration work does not yet model
  snapshots (stage B8, `notes/STATUS.md`).
- **Possible fixes**: raft knows which entry an `ApplyConfChange` call is for once it tracks
  the conf entries it hands out; `raft-conf-lag-model/guard-fix.patch` does so
  (`Config.TrackConfChangeApplication`) and ignores a call for an entry at or below the last
  restored snapshot's index (`TestConfChangeLagSnapshotDuringApply`). Without tracking:
  refuse to restore a snapshot while `applying > applied` (the follower answers as for an
  ignored snapshot and the leader retries, only after `ReportSnapshot`), at the cost of delaying
  catch-up; keep the `MsgSnap` while `applying > applied` and step it again when `appliedTo` brings
  `applied` to `applying` (2026-10-18; the leader sends the snapshot again if the follower answers
  a probe meanwhile, or if the term changes); restore at once but keep the configuration the
  restore replaced while the older entries are being applied, apply the `ApplyConfChange` calls
  made meanwhile to it and return its `ConfState`, and hand out no newer entries until then (with
  `AsyncStorageWrites`, so that no call can be for one; 2026-10-21, replaced); or, the candidate's fix
  (2026-10-21), switch raft's configuration to the snapshot's when the snapshot is applied
  (`appliedSnap`) instead of when it is restored, so that the configuration is always the one at
  the applied index. With `AsyncStorageWrites` that needs the snapshot applied after the committed
  entries handed out before it, which `raft-async-snapshot-during-apply-divergence.md`'s fix (hand
  nothing to the append thread while the snapshot waits for them) provides; the candidate leaves that
  mode to it.
- **Found**: 2026-10-14, while working out how the guard fix should treat snapshot restores
  (`raft-conf-lag-model/guard-fix.md`), reproduced by the tests above.
