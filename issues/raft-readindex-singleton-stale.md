# raft: `ReadOnlySafe` read index answers stale reads at a single-voter configuration reached by a configuration change

- **Status**: open (not reported upstream).
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
- **How the proof handles it**: the static read-index proof excludes the path by the premise
  `1 < size cfg` of `raft.Step`/`node.ReadIndex` (`notes/STATUS.md`, "Read-index"). Under
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
