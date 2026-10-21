---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/raft#354 issue open: related, not this bug (a rejected ConfChange becomes a silent no-op; same pendingConfIndex guard, no Advance/apply ordering)
---

# etcdserver: the leader calls raft's Advance before its apply loop has applied a conf change, which lets raft accept an overlapping membership change

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
