---
upstream: fixed
checked: 2026-10-20
links:
  - etcd-io/raft#533 issue closed: this bug, reported 2026-10-19; closed by #535
  - etcd-io/raft#535 pr merged: the fix, opened and merged 2026-10-19 (ahrtr: no backport, "usually it won't happen in production")
  - etcd-io/raft@1d3216d84: #535's merge commit, on `main`
  - etcd-io/raft#392 issue closed: related, not this bug (the user's: ReadIndex retries with a reused rctx; not the IsSingleton shortcut)
  - etcd-io/raft#397 pr closed: related, not this bug (the user's: unique heartbeat ctxes for read-only requests)
  - etcd-io/raft#398 pr closed: related, not this bug (the user's: document not retrying ReadIndex with the same rctx)
  - etcd-io/raft#83 issue open: related, not this bug: make StepDownOnRemoval the default (would remove the removed-leader half of the scenario, not the commit-index half)
candidate: issues/upstream/raft-readindex-singleton-stale/
---

# raft: `ReadOnlySafe` read index answers stale reads at a single-voter configuration reached by a configuration change

- **Upstream, split in two** (2026-10-18): this candidate reports execution 1 (a new single-voter leader before its
  first commit in its term); execution 2 (a removed leader) is
  [raft-readindex-removed-leader](raft-readindex-removed-leader.md), with its own candidate and fix branch.
- **Status**: fixed upstream by etcd-io/raft#535 (merged 2026-10-19, `1d3216d84`; not backported). Before that,
  fixed in a fork commit, verified at `raft.Step` (2026-10-14, stage F): `0560cb7` (etcd-io/raft
  `40f8be7` plus the fix of `raft-conf-lag-model/readindex-singleton-fix.patch` and regression
  tests `readindex_singleton_test.go`, which fail without it), saved as
  `raft-conf-lag-model/0001-raft-readindex-singleton-fix.patch` (`git am` on `40f8be7`), pushed
  as branch `raft-goose-lean` of `upamanyus/etcd` (a branch holding etcd-io/raft's history), from
  which the proof's raft pin (`etc/goose.py`, project `etcd-raft`) is taken since 2026-10-14
  (the register's `go.mod` replaces `go.etcd.io/raft/v3` by it).
  **Also in v3.7.0** (2026-10-15), the raft etcd links (`go.etcd.io/raft/v3 v3.7.0` in etcd's
  `go.mod`, etcd-io/raft `b867cf13`): `raft.go:1355-1361` has the same unconditional
  `IsSingleton` shortcut. The fix rebased onto v3.7.0's pointer messages is `509271dac` on branch
  `raft37-goose-lean` (to be pushed to `upamanyus/etcd`), saved as
  `raft-conf-lag-model/0001-raft-readindex-singleton-fix-v3.7.0.patch`, with the regression tests
  adapted to `*pb.Message` and getters (they fail without the fix; `go test ./...` passes); it is
  the pin of `etc/goose.py`'s project `raft37`, the retarget of the proof (`notes/raft-retarget-plan.md`).
- **Where** (etcd-io/raft at `40f8be730b18`, the revision `etc/goose.py` pins):
  - `raft.go:1341-1348` (`stepLeader`, `MsgReadIndex`): `if r.trk.IsSingleton()` answers at
    once with `r.raftLog.committed`. This runs *before* the `committedEntryInCurrentTerm`
    check of `raft.go:1350-1355`, which the multi-voter path needs and gets, and it does not
    check that the single voter is the leader itself.
  - `tracker/tracker.go:160-162` (`IsSingleton`): `len(Voters[0]) == 1 && len(Voters[1]) == 0`,
    whoever that voter is.
  - `raft.go:1986-1994` (`switchToConfig`): a removed leader stays leader unless
    `StepDownOnRemoval` (default false, `raft.go:280-285`).
  - The comment says "only one voting member (the leader) in the cluster": both of its
    assumptions (that the voter is the leader; that the leader's commit index is current)
    fail once configurations change.
- **What happens**: two executions, both with applications that apply every conf change
  before `Advance`, synchronous storage, no restart.
  1. *New leader, before its first commit.* `C0 = {1,2}`; node 2 leads term 1, proposes
     `remove 2` (index 2) and then `x` (index 3, before it applies its removal). Node 1 learns
     that index 2 is committed (and applies it: configuration `{1}`) but the messages telling
     it that index 3 is committed are lost; node 2 commits and applies `x`. Node 1 wins term 2
     on its own vote; a `ReadIndex` stepped before its next `Advance` (before its empty entry
     commits) gets `ReadState{Index: 2}`, which misses `x`, committed and applied before the
     read was issued.
  2. *Removed leader.* The same start; node 2 is still leader of term 1 with configuration
     `{1}`, so `IsSingleton` holds although node 2 is not a voter. Partition `{1} | {2}`: node 1
     wins term 2 alone and commits `y` (index 5). A `ReadIndex` at node 2 is answered at once
     with node 2's commit index 3: a stale read with no bound on its staleness (node 2 never
     learns it is deposed, since nothing confirms its leadership).

  A `ReadOnlySafe` leader answers a read only after two checks: it has committed an entry of its
  own term (so its commit index is current), and a quorum has acknowledged a heartbeat sent after
  the request arrived (so it is still leader). The shortcut skips both, and `IsSingleton` does not
  ask who the one voter is:

  ```go
  // raft.go:1341-1359 (etcd-io/raft 40f8be7)
  	case pb.MsgReadIndex:
  		// only one voting member (the leader) in the cluster
  		if r.trk.IsSingleton() { // <-
  			if resp := r.responseToReadIndexReq(m, r.raftLog.committed); resp.To != None { // <-
  				r.send(resp)
  			}
  			return nil
  		}

  		// Postpone read only request when this leader has not committed
  		// any log entry at its term.
  		if !r.committedEntryInCurrentTerm() {
  			r.pendingReadIndexMessages = append(r.pendingReadIndexMessages, m)
  			return nil
  		}

  		sendMsgReadIndexResponse(r, m)

  		return nil
  ```

  ```go
  // tracker/tracker.go:158-162 (etcd-io/raft 40f8be7)
  // IsSingleton returns true if (and only if) there is only one voting member
  // (i.e. the leader) in the current configuration.
  func (p *ProgressTracker) IsSingleton() bool {
  	return len(p.Voters[0]) == 1 && len(p.Voters[1]) == 0 // <-
  }
  ```

  Reproduction: `raft-conf-lag-model/readindex_singleton_test.go` (in package `raft`; public
  `RawNode` API, `discardLogger` aside), which passes by asserting the stale read:

      cp issues/raft-conf-lag-model/readindex_singleton_test.go <etcd-raft checkout>/
      cd <etcd-raft checkout> && go test -run TestReadIndexSingleton -v .
      ...
      STALE READ reproduced: read index 2 at node 1 (term 2), but x was committed at index 3 before the read
      STALE READ reproduced: removed leader 2 answered read index 3; y was committed at index 5 (term 2) before the read

  With a fixed voter set neither happens (the only voter is the leader and every commit is its
  own), which is why the static proof could exclude the path by a premise.
- **Expected**: `ReadOnlySafe` read index is linearizable (`ReadOnlySafe`'s documentation,
  `raft.go`'s `ReadOnlyOption`): the answer covers every entry committed before the request.
- **Verified (2026-10-14, stage F)**: with the pin at `0560cb7`, `raft.Step.spec` takes a
  `MsgReadIndex` at any configuration, in both ghost modes (static and dynamic): its premise
  `¬ (size c.incoming = 1 ∧ size c.outgoing = 0)` is gone, and so are `stepLeader`'s. The
  shortcut is a model rule (`StepC`/`StepR.readSingle`, `readReleaseSingle`: at a configuration
  whose only voter is the leader, with an entry of its term committed), refined like the heartbeat
  path with the quorum `{id}`: the leader's own acknowledgement confirms its record
  (`ownRaftGhost_single_confirm`, `Protocol/Refinement.lean`). What remains is at the public API
  (stage B7 part 2's files): `RawNode.Step.spec`'s and `RawNode.ReadIndex.spec`'s read-index
  premise (`NotSingleton`), `node.ReadIndex`'s and the register's `1 < size reCfg`, and the static
  `raft.Step.specS`'s `1 < GMap.size cfg` (kept for its callers), none of which `raft.Step` needs
  any more (`notes/status-history.md`, "The single-voter read-index fix").
- **How the proof handled it until 2026-10-14**: the static read-index proof excluded the path by the premise
  `1 < size cfg` of `raft.Step`/`node.ReadIndex` (`notes/status-history.md`, "Read-index"). Under
  reconfiguration the configuration is not the caller's to fix, so the premise becomes a
  restriction on the run (no configuration with a single incoming voter and no outgoing half
  while a leader may receive `MsgReadIndex`), or the code is fixed. The reconfiguration paper
  proof (`notes/reconfiguration-safety.md` section 8) does not mention the path; see
  `notes/reconfiguration-safety-review.md`.
- **Possible fixes**: `raft-conf-lag-model/readindex-singleton-fix.patch` moves the singleton
  shortcut into `sendMsgReadIndexResponse`, after the `committedEntryInCurrentTerm` check
  (postponed requests are released through the same function), and takes it only if the
  single voter is `r.id`; otherwise the request goes through the heartbeat round (a removed
  leader then needs the actual voter's acknowledgement). With it both tests above fail (no
  stale read; the removed leader's read is never confirmed while partitioned) and `go test
  ./...` passes otherwise. Setting `StepDownOnRemoval` removes execution 2 only.
- **etcd**: etcd stops a member that removes itself (execution 2 does not arise); execution 1
  may be reachable when a cluster is scaled down to one member and a linearizable read
  arrives right after that member's election (`server/etcdserver/read/read.go` takes the
  first matching `ReadState`): not demonstrated.
- **Found**: 2026-10-14, adversarial review of the reconfiguration paper proof
  (`notes/reconfiguration-safety-review.md`, read index), reproduced by the test above.
