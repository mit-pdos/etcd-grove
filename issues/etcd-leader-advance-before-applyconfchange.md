---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/raft#354 issue open: related, not this bug (a rejected ConfChange becomes a silent no-op; same pendingConfIndex guard, no Advance/apply ordering)
candidate: issues/upstream/etcd-leader-advance-before-applyconfchange/
---

# etcdserver: the leader calls raft's Advance before its apply loop has applied a conf change, which lets raft accept an overlapping membership change

**2026-10-25: fixed in the fork** (D43 M3): branch `goose-lean-leaderwait` of `upamanyus/etcd` (`4d9282b0f`, on
`bc9c3868c`, the pin of `etc/goose.py`) adds the follower's second `notifyc` send to the leader branch of
`raftNode.start` (the upstream candidate's fix) and runs `TestConfigChangeBlocksApply` for the leader too (it fails
without the fix). The proof needs it: in raft's dynamic mode `node.Advance` asks that a `Ready`'s conf entries be
applied first (A1).

**2026-10-23 (investigation: a bad execution is possible, nothing in etcd prevents it; still not reproduced end-to-end).**
Re-checked against upstream `main` 3aaab3479 and `go.etcd.io/raft/v3` v3.7.0. Verdict: **no etcd check or ordering
closes the window** — the leader-lag safety violation (two overlapping membership changes both applied, giving
disjoint quorums and a divergent/lost committed entry) is reachable in principle. It is not prevented; it is only
made unlikely by timing. Details:

- *The contract gap is live at HEAD.* `TestConfigChangeBlocksApply`, run for `StateLeader` as well as
  `StateFollower` (the fix branch's test, cherry-picked onto `main` 3aaab3479), still fails for the leader:
  `raft_test.go:251 unexpected execution: raft routine should block waiting for toApply`; the follower passes. The
  leader branch of `raftNode.start` (`server/etcdserver/raft.go`, the `else` at the `notifyc <- struct{}{}` after
  the `confChanged` scan) sends `notifyc` once and calls `r.Advance()` with no wait, unchanged from the draft's
  base. So `raftLog.applied` moves before the apply loop runs `ApplyConfChange`.
- *The raft mechanism is real at v3.7.0.* The propose-time guard is `alreadyPending := r.pendingConfIndex >
  r.raftLog.applied` (`raft.go:1326`, v3.7.0); `DisableConfChangeValidation` is **off** in etcd (`raftConfig`,
  `server/etcdserver/bootstrap.go:564`, default config: `CheckQuorum` true, no `DisableConfChangeValidation`), so
  this guard is the only propose-time protection and `Advance` defeats it. The raft `Node` reproduction
  `TestNodeAdvanceBeforeApplyConfChange` (branch `raft-advance-before-applyconfchange-repro`, commit 3dcedb6,
  three nodes) commits two *different* entries at index 4 through the public `Node` API.
- *No etcd apply-time defense turns the second change into a no-op.* `applyConfChange` →
  `cluster.ValidateConfigurationChange` (`server/etcdserver/api/membership/cluster.go:306`) validates each conf
  change against the membership store **as sequentially updated by the conf changes already applied in log order**
  (existence / already-removed / peer-URL conflicts). It has no notion of a pending or unapplied conf change, so
  when a node applies `C1=add 4` then `C2=remove 2` in log order each passes and `C2` is a *real* removal, applied
  through `s.r.ApplyConfChange`. The membership API guards that run *before* proposing (`mayAddMember`/
  `mayRemoveMember`, `isLearnerReady`) read the applied membership and peer health and **do not serialize two
  concurrent clients**; `configure`'s `<-resp.raftAdvanceC` wait serializes one client's *sequential* changes only
  (its own request). None of these look at raft's `pendingConfIndex`/`applied` relationship.
- *Reachable schedule (add-member route; gives disjoint quorums).* Cluster `{1,2,3}`, leader 1, apply loop
  stalled on the leader (large batch / slow backend commit / defrag; a `beforeApplyOneConfChange` failpoint in a
  test). (a) client A `MemberAdd(4, started)` → `mayAddMember` ok on `{1,2,3}` → `configure` proposes `C1=add 4`,
  committed at index 2 by `{1,2}` (`server.go:1376`, `1749`); leader's `Ready` takes the leader branch and calls
  `r.Advance()` → `applied=2`, but raft config still `{1,2,3}` (`raft.go:331`). (b) concurrent client B
  `MemberRemove(2)` → `mayRemoveMember` ok on store `{1,2,3}` → proposes `C2=remove 2`; `stepLeader` MsgProp:
  `pendingConfIndex(2) > applied(2)` is false → accepted, committed at index 3 under `{1,2,3}` by `{1,2}`
  (`raft.go:1326`). (c) nodes 3 and 4 receive indices 1–3 with commit 3 and apply both → config `{1,3,4}`. (d)
  leader (still `{1,2,3}`) commits `x` at index 4 by `{1,2}`. (e) partition `{1,2}|{3,4}`: `{1,2}` is a majority of
  `{1,2,3}` and `{3,4}` a majority of `{1,3,4}`, and the two sets are **disjoint** → node 3 wins with `{3,4}` and
  commits a different entry at index 4. Two committed entries at one index ⇒ lost committed data. `C2` is committed
  by `{1,2}`, which is *not* a majority of `{1,2,3,4}` (the config in effect after `C1`): the Raft invariant that
  consecutive configs share the commit quorum is broken. (A secondary route — leader steps down after `Advance`,
  before applying, and campaigns with the unapplied change — hits `hasUnappliedConfChanges`/`becomeLeader` the same
  way; it can also reach the `r.trk.Progress[r.id]` nil panic when a node removed from its own config campaigns.)
- *Why it stays hard to hit (honest caveat; why no cluster reproduction here).* The window is normally sub-millisecond
  and needs the leader's apply loop stalled across it; it needs two conf-change clients concurrent (or one forwarded);
  and the add-member route needs node 4 to catch up and vote on the `{3,4}` side, yet the leader only `transport.AddPeer(4)`s
  when it applies `C1` — so during the stall node 4 is fed only once node 3 (whose apply loop is not stalled) applies
  `C1`/`C2`, becomes leader and replicates/snapshots to 4. A gofail integration test (failpoint `beforeApplyOneConfChange`
  to hold the leader apply, `MemberAdd(4)` + concurrent `MemberRemove(2)`, then the partition and an election on 3) is a
  large, racy effort and was not built in this pass; the evidence above (contract test at HEAD + raft `Node` reproduction
  + the code reading that no etcd check closes the gap) establishes possibility without it. Same analysis holds with
  `--strict-reconfig-check=off` (the `may*` checks are skipped, so the race is *easier*), and for the v2 and v3 membership
  paths and learner promote, since all route through `configure`/`ProposeConfChange` and the same leader branch.

**2026-10-21**: candidate `issues/upstream/etcd-leader-advance-before-applyconfchange/` (on hold until the raft
documentation PR is accepted): `TestConfigChangeBlocksApply` run for a leader fails at etcd `main` 7ff040cb8 (the
leader's raft loop calls `Advance` before its apply loop has applied the conf change); the fix makes the leader
wait as followers do. Still no wrong result reproduced on an etcd cluster.

**Status of this draft**: unconfirmed in etcd. The two ingredients are confirmed (the first by
reading etcd's code, the second by a Go test on raft); the end-to-end violation has not been
run on etcd. Not filed.

## Summary

raft's guard against overlapping configuration changes (a leader accepts a conf change only
if `pendingConfIndex <= applied`) goes by raft's applied index, which `Advance` moves, while
the configuration only changes when the application calls `ApplyConfChange`. If `Advance`
comes first, a leader accepts a second conf change while it still uses the configuration
before the first, and two different entries can be committed at the same index (raft issue
#TODO, reproduced through raft's public `RawNode` API). etcd's raft loop waits for the apply
loop before `Advance` on followers and candidates when the `Ready` has a conf change, and its
comment names this hazard, but it does not wait on the leader. So on the leader there is a
window, as long as its apply loop is behind, in which a second membership change proposed
concurrently (by another client, or forwarded by another member) is accepted by raft under
the old configuration. We found this while formally verifying etcd-raft's reconfiguration.

## What happens

References are to etcd as of the `upamanyus/etcd` fork's `goose-lean` branch at
bc8b52a50 (upstream `main` of 2026-10 plus the commits that make it translatable; check these
lines against upstream when filing) and to `go.etcd.io/raft/v3` v3.7.0, which etcd's
`server/go.mod` requires.

1. `raftNode.start` (`server/etcdserver/raft.go:185-336`) hands each `Ready`'s committed
   entries to the apply loop (`r.applyc <- ap`, line 232), saves to the WAL, and then:
   - not leader (lines 297-324): if the `Ready` has a conf change entry, it blocks until
     `applyAll` has applied the batch (the second `notifyc` send, lines 312-321), with the
     comment "Candidate or follower needs to wait for all pending configuration changes to
     be applied before sending messages. Otherwise we might incorrectly count votes (e.g.
     votes from removed members). Also slow machine's follower raft-layer could proceed to
     become the leader on its own single-node cluster, before toApply-layer applies the
     config change.";
   - leader (lines 325-328): only `notifyc <- struct{}{}`;
   and then calls `r.Advance()` (line 331) in both cases.
2. The apply loop applies the conf change later: `EtcdServer.apply`
   (`server/etcdserver/server.go:1917-1925`) → `applyConfChange` → `s.r.ApplyConfChange(cc)`
   (line 2023).
3. In raft v3.7.0, `Advance` steps the `MsgStorageApplyResp` that moves `applied`
   (`rawnode.go`), and the leader's check is `alreadyPending := r.pendingConfIndex >
   r.raftLog.applied` (`raft.go:1326`). Between steps 1 and 2 it is false for the committed
   but unapplied conf change.
4. etcd's own checks before proposing (`AddMember`/`RemoveMember`, `mayAddMember`/
   `mayRemoveMember`, `server.go:1376-1450`, 1602-1645) look at the member's applied
   membership and at peer health; they do not serialize membership changes. `configure`
   (`server.go:1749-1786`) waits, for its own request, until the change is applied and raft
   has advanced (the `raftAdvanceC` wait added for #15528), which serializes one client's
   sequential changes but not two concurrent ones.

The raft loop's two branches (the lines are the same in etcd `main` at f061acd09):

```go
// server/etcdserver/raft.go:289-331 (etcd main f061acd09)
				confChanged := false
				for _, ent := range rd.CommittedEntries {
					if ent.GetType() == raftpb.EntryConfChange {
						confChanged = true
						break
					}
				}

				if !islead {
					// ...
					// Candidate or follower needs to wait for all pending configuration
					// changes to be applied before sending messages.
					// Otherwise we might incorrectly count votes (e.g. votes from removed members).
					// Also slow machine's follower raft-layer could proceed to become the leader
					// on its own single-node cluster, before toApply-layer applies the config change.
					// ...
					if confChanged { // <- the follower waits for the apply loop
						// ...
						select {
						case notifyc <- struct{}{}:
						case <-r.stopped:
							return
						}
					}
					// ...
				} else {
					// leader already processed 'MsgSnap' and signaled
					notifyc <- struct{}{} // <- the leader does not
				}

				// gofail: var raftBeforeAdvance struct{}
				r.Advance() // <-
```

and the guard in raft v3.7.0 that `Advance` defeats:

```go
// raft.go:1326 (go.etcd.io/raft/v3 v3.7.0), stepLeader, MsgProp
				alreadyPending := r.pendingConfIndex > r.raftLog.applied // <-
```

An example execution, with members 1, 2 and 3 and member 1 the leader:

1. A client's `MemberAdd` of member 4 commits `C1 = add 4` at index 2 with `{1,2}`. Member 1's
   raft loop takes the leader branch: it signals the apply loop and calls `Advance`, so raft's
   applied index is 2. Member 1's apply loop is still behind (a large batch, a slow backend
   commit, a defragmentation), so raft's configuration is still `{1,2,3}`.
2. A concurrent `MemberRemove(2)` reaches raft. `pendingConfIndex` (2) is not above applied
   (2), so raft accepts `C2 = remove 2` at index 3 and commits it under the old configuration
   `{1,2,3}` with `{1,2}`.
3. Members 3 and 4 receive indices 1-3 with commit 3 and apply both changes (configuration
   `{1,3,4}`).
4. Member 1, still on `{1,2,3}`, commits `x` at index 4 with `{1,2}`.
5. Partition `{1,2} | {3,4}`. Member 3 has applied all it committed, so it may campaign. It
   wins with `{3,4}`, a majority of `{1,3,4}`, and commits a different entry at index 4.

raft issue #TODO reproduces steps 1-5 on raft alone.

A second route with the same window: a leader that steps down (check quorum) after
`Advance` but before its apply loop applied a conf change campaigns as a follower with the
conf change committed and unapplied; raft's campaign guard (`hasUnappliedConfChanges`,
`raft.go:995-1000` in v3.7.0) scans only `(applied, committed]`. The follower-path wait does
not cover it, since the `Ready` with the conf change was handled as leader. With one
unapplied single change the old and new configurations still have intersecting majorities;
the unsafe case needs two, which in etcd needs the first route too.

## How to reproduce

Not run on etcd. On raft, `TestAdvanceBeforeApplyConfChangeLeaderLag` (raft issue #TODO)
drives the execution through `RawNode` with node 1 doing what etcd's leader does (`Advance`,
then `ApplyConfChange` later) and the others what etcd's followers do. An etcd integration
test would need: a 3-member cluster; the gofail failpoint `beforeApplyOneConfChange`
(`server.go:1918`) set to sleep on the leader; a `MemberAdd` (member 4, started) and, while
the leader sleeps, a concurrent `MemberRemove(2)`; a write committed by members 1 and 2 with
3 and 4 cut off; then the partition `{1,2} | {3,4}` and an election on member 3's side. One
etcd-specific point to check there is that member 4, which joins from the leader's snapshot
or log, votes for member 3 (it has no leader lease, so `CheckQuorum` does not stop it).

## Expected

A leader does not accept a conf change while one is committed but not applied to its raft
configuration, as on followers.

## Proposed fix

Make the leader wait as the followers do when the `Ready` has a conf change entry, before
`Advance` (`server/etcdserver/raft.go`, the leader branch):

```go
} else {
	// leader already processed 'MsgSnap' and signaled
	notifyc <- struct{}{}
	// As on followers: raft's guard against overlapping configuration changes
	// reads the applied index, which Advance moves; the configuration only
	// changes when the apply loop calls ApplyConfChange.
	if confChanged {
		select {
		case notifyc <- struct{}{}:
		case <-r.stopped:
			return
		}
	}
}
```

The cost is that the leader's raft loop waits for its apply loop on batches with a
membership change, which are rare. Alternatively, if raft adopts the option proposed in
raft issue #TODO (`Config.TrackConfChangeApplication`), etcd can set it; it then has to call
`ApplyConfChange` with a zero `NodeId` for the replayed conf entries it now skips after a
restart (`server.go:2018-2024`), or those members could never campaign again.
