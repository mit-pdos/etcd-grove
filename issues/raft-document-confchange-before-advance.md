# raft: document that a Ready's conf changes must be applied before Advance, and that entries and HardState must be persisted atomically

## Summary

`doc.go` allows an application to call `Advance` "at any time after step 1", that is, before
it has finished applying the committed entries of the `Ready`, and `Node.Advance` repeats the
permission ("the application may call Advance while it is applying the commands"). For
configuration changes this permission is unsafe: raft's guards against overlapping
configuration changes go by the applied index, which `Advance` moves, while the
configuration only changes in `ApplyConfChange`. An application that calls `Advance` before
`ApplyConfChange` lets a leader accept a second conf change while it still uses the
configuration before the first, and lets a node campaign with a committed conf change it has
not applied. Two different entries can then be committed at the same index; we reproduce
this with the public `RawNode` API only. The same window lets a node whose own removal is
committed campaign, be removed while a candidate, win, and crash in `becomeLeader`.

A second, related precondition is also unstated: the election guard reads the persisted
commit index after a restart, so entries persisted without the `HardState` that commits them
can hide a committed conf change from it.

We found both while formally verifying etcd-raft's reconfiguration. We ask for the
documentation to state the preconditions; a separate issue proposes a code change that
removes the first one (#TODO, "raft: track which conf changes have been applied").

## What happens

References are to `main` at 40f8be730b18.

The guards:

- `hasUnappliedConfChanges` (`raft.go:990-1020`, called from `hup`, `raft.go:978`) refuses
  a campaign when a conf change entry is in `(applied, committed]`.
- The leader accepts a conf change proposal only if
  `alreadyPending := r.pendingConfIndex > r.raftLog.applied` is false (`raft.go:1313`).

`applied` moves on `Advance` (`rawnode.go:482-494` steps the `MsgStorageApplyResp`, whose
handler calls `appliedTo`, `raft.go:1192-1196`), or with `AsyncStorageWrites` when the
application steps that response. The configuration only changes in `ApplyConfChange`
(`raft.go:1939-1958`). Between the two, both guards treat the conf change as applied while
the node still uses the old configuration.

The documentation that allows the window: `doc.go:100-102` (step 4: "Call Node.Advance() to
signal readiness for the next batch of updates. This may be done at any time after step 1",
where step 3 applies the committed entries, `ApplyConfChange` included) and `node.go:166-174`
(`Advance`: "as an optimization, the application may call Advance while it is applying the
commands").

An execution (one lagging node suffices, the leader). `C0 = {1,2,3}`, node 1 leads term 1:

1. Node 1 commits `C1 = add 4` (index 2) with `{1,2}`. Its application calls `Advance` for
   that `Ready` but has not yet called `ApplyConfChange(C1)`: applied = 2, configuration
   `C0`.
2. Node 1 proposes `C2 = remove 2`. The guard reads `pendingConfIndex (2) > applied (2)`:
   false, so it is accepted at index 3, and commits under `C0` with `{1,2}`.
3. Nodes 3 and 4 receive indices 1-3 with commit 3 and apply both changes (before `Advance`):
   configuration `{1,3,4}`.
4. Node 1, still on `C0`, commits `x` at index 4 with `{1,2}`.
5. Partition `{1,2} | {3,4}`. Node 3 campaigns (applied = committed = 3, no unapplied conf
   change) and wins term 2 with `{3,4}`, a majority of `{1,3,4}`; it commits its empty
   entry at index 4.

Index 4 is committed as `x` on node 1 and as node 3's empty entry on nodes 3 and 4.

A variant without a lagging leader: a follower receives `C1` and `C2` committed, calls
`Advance` past both without applying them, and wins an election under `C0` with `{1,2}`
after `x` was committed at index 4 by `{3,4,5}` under `{1,2,3,4,5}`.

A crash: if node 3 (any follower) calls `Advance` past its own committed removal, it may
campaign (no conf change in `(applied, committed]`); when its application then calls
`ApplyConfChange`, it stays a candidate outside its configuration (`switchToConfig`,
`raft.go:1967-1991`, only steps down a removed *leader*). If the remaining voters grant their
votes it wins, and `becomeLeader` (`raft.go:942-943`, `r.trk.Progress[r.id].BecomeReplicate()`)
dereferences a nil `Progress`.

Atomic persistence. After a restart the scan of `hasUnappliedConfChanges` covers
`(applied, committed]` with the commit index of the persisted `HardState`. `doc.go:74-76`
(step 1) asks to write `HardState`, `Entries` and `Snapshot` but not atomically. A node that
persists entries including a committed conf change but crashes before the `HardState` that
commits it restarts with a lower commit index and an older configuration, sees no unapplied
conf change, and can win an election under the old configuration after a different entry
was committed under the new one (`C0 = {1,2,3}`; leader 3 commits `C1 = add 4`; node 1
persists indices 1-3 but not commit 2, restarts on `C0`; `C2 = remove 2` commits on `{1,3,4}`
and `x` at index 4 with `{3,4}`; node 1 wins with node 2's vote and overwrites index 4). This
one we have only in an abstract model of the protocol, not as a Go test.

## How to reproduce

`TestAdvanceBeforeApplyConfChangeLeaderLag` (attached, `leaderlag_test.go`, package `raft`)
drives the leader-lag execution above through `RawNode` (`Campaign`, `Propose`,
`ProposeConfChange`, `Ready`, `Advance`, `ApplyConfChange`, `Step`) with `MemoryStorage` and
synchronous storage writes, routing messages by hand. The only deviation from a textbook
application is that node 1 calls `Advance` before `ApplyConfChange`, which the documentation
allows. It passes by asserting the violation:

```
go test -run TestAdvanceBeforeApplyConfChangeLeaderLag -v .
...
SAFETY VIOLATION reproduced: index 4 committed as "x" (term 1) on node 1 and as "" (term 2) on node 3
```

`TestRemovedCandidateWinsAndPanicsRawNode` (attached, `removed_candidate_rawnode_test.go`,
uses the harness of `leaderlag_test.go`) shows the crash through `RawNode`:

```
go test -run TestRemovedCandidateWinsAndPanicsRawNode -v .
...
node 3: StateCandidate, config voters=(1 2)
PANIC reproduced: runtime error: invalid memory address or nil pointer dereference
```

With every application calling `ApplyConfChange` before `Advance`, neither execution is
possible: in the first, node 1 moves to `{1,2,3,4}` before proposing `C2`, which its guard
then refuses until it is applied; in the second, node 3 cannot campaign until it has
applied its removal, after which it is unpromotable.

(The test's node 4 starts with empty storage while nodes 1-3 have the initial `ConfState`
in an index-0 snapshot, so node 4's configuration is built from the changes alone. That is
a separate problem, reported as #TODO; the violation above does not depend on it: node 3,
whose configuration is right, is the one that wins.)

## Expected

The documentation states what the guards need:

- `doc.go` step 4, `Node.Advance`, `RawNode.Advance`: the configuration changes of a `Ready`
  must have been applied (`ApplyConfChange`) before `Advance` is called for it; the
  "Advance while applying" optimization applies to the other entries and to snapshots only.
- `Config.AsyncStorageWrites`: likewise, `ApplyConfChange` for the conf changes of a
  `MsgStorageApply` must be called before its `MsgStorageApplyResp` is stepped.
- `doc.go` step 1: the entries and the `HardState` of a `Ready` must be persisted
  atomically. (Neither order works without it: entries first is the execution above;
  `HardState` first can leave a commit index past the last persisted entry, which raft
  refuses on restart.) In plain Raft the commit index is volatile; here it is not, because
  the election guard reads it.

A related inconsistency to fix at the same time: `doc.go:94-98` says `ApplyConfChange` "must
be called one way or the other" (a rejected change is passed with its `NodeId` zeroed),
while `Node.ApplyConfChange` (`node.go:179-187`) and `RawNode.ApplyConfChange`
(`rawnode.go:109-111`) say that for a rejected change it "must not be called".

## Proposed fix

Documentation only (wording above). A code change that makes the first precondition
unnecessary is proposed separately (#TODO): raft tracks which handed-out conf changes have
been passed to `ApplyConfChange` and uses that in both guards.
