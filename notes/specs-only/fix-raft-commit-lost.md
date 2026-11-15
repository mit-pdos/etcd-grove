# Fixing raft-commit-lost-with-entries-kept on the Goose fork (open question 2.8, §6 F8)

2026-11-10. The bug: `issues/raft-commit-lost-with-entries-kept.md` (a crash after a `Ready`'s
entries are written and before its `HardState` lets a node holding two committed conf changes above
its stored commit win an election in its old configuration). The user's 2.8 answer: fix on the fork,
then prove; the conf-change part of `Wal.crashInScope` goes. This note is the Go side only: no Lean,
no re-translation yet.

**Result.** A raft-side fix in `hasUnappliedConfChanges`: besides a conf change in
`(applied, committed]`, the campaign guard refuses a node whose log holds **two or more** conf
changes above `committed`. Local branch `raft37-goose-lean-a3` of a clone of the fork, commit
`79ff9c5f626ca8285c77e1550a40bbca32b04772` on `raft37-goose-lean-a2` (`565c2bd`), at
`/home/ubuntu/.claude-E/jobs/b4c3a1d2/tmp/raft-fix` (not pushed). `go test ./...` passes, `-race`
too; no existing test changes. The alternative from `fix-plan.md` R1 (a restart infers the commit
index) was implemented as a scratch variant and compared (section 4); the guard is the choice.

## 1. The fix

```diff
@@ func (r *raft) hasUnappliedConfChanges() bool {
-	if r.raftLog.applied >= r.raftLog.committed { // in fact applied == committed
+	committed := r.raftLog.committed
+	hi := committed + 1
+	if !r.disableConfChangeValidation {
+		hi = r.raftLog.lastIndex() + 1
+	}
+	lo := r.raftLog.applied + 1
+	if lo >= hi {
 		return false
 	}
 	found := false
-	lo, hi := r.raftLog.applied+1, r.raftLog.committed+1
+	confAboveCommit := false
 	pageSize := r.raftLog.maxApplyingEntsSize
 	if err := r.raftLog.scan(lo, hi, pageSize, func(ents []*pb.Entry) error {
 		for i := range ents {
 			if ents[i].GetType() == pb.EntryConfChange || ents[i].GetType() == pb.EntryConfChangeV2 {
-				found = true
-				return errBreak
+				if ents[i].GetIndex() <= committed || confAboveCommit {
+					found = true
+					return errBreak
+				}
+				confAboveCommit = true
 			}
 		}
 		return nil
```

plus a doc comment on the function (the argument of section 2 in five sentences). `hup` is
unchanged (it still logs "cannot campaign ... pending configuration changes to apply").

**Why not the issue's first suggestion** (refuse while *any* conf change is above `applied`): it
deadlocks a crash-free cluster. A leader commits a conf change and dies before the followers learn
that it did; every follower holding the change refuses to campaign, and nobody is left to tell them
the commit index. `TestCampaignWithUncommittedConfChange` (below) is that execution: it fails with
the whole-log variant (checked: `if true || ...`, `hi = lastIndex+1` unconditionally; no existing
raft test fails with it, so the suite alone would not have caught the regression). The one-change
allowance is exactly what raft already relies on: a single conf change above the commit is the
"adjacent configurations" case, whose majorities overlap.

**`DisableConfChangeValidation`.** With the flag the leader does not enforce one pending conf
change (`stepLeader`, `raft.go:1344-1357`: `alreadyPending` is computed but ignored), so a
crash-free log may hold several uncommitted conf changes, and the new clause would block a campaign
the application considers safe (the flag's users serialize changes above raft). The flag keeps the
old scan of `(applied, committed]`. etcd does not set it; our `ConfigOk` requires it off
(`SpecPlan/Spec/go_etcd_io/raft/v3/Api.lean:537`).

**Goose.** The changed function uses only what the pinned one already did and the translation
already covers (`Code/go_etcd_io/raft/v3.lean:6110ff`: a closure passed to `scan` that writes a
captured local, `errBreak`): two more locals (one captured read-only, one written), a method call
`lastIndex()`, a field read `r.disableConfChangeValidation`, `||`. No new package, generics or
language feature; `Code/go_etcd_io/raft/v3.toml` translates every function, so nothing to configure.

## 2. Safety

The claim: no index is committed with two different entries, whatever crash point a `Ready` is cut
at between its entries and its `HardState` (any prefix of the entries kept, the old `HardState`
kept), given the paper proof for crash-free runs (`notes/reconfiguration-safety.md`).

1. **The fix only removes behaviors.** It refuses a campaign the pinned code allows and allows none
   it refuses; a refused `hup` changes no state. So any safety argument for the pinned code's
   crash-free runs carries over, and in those runs the answer is unchanged (item 3).
2. **What a crash breaks, and where it was used.** A restart from the cut state is a crash-free
   state of the node except for the commit index: the log is the old log with a prefix of the
   batch's entries (a valid log: log matching holds), applied and configuration are the snapshot's,
   and the commit is the old one, lower than the one the node held in memory (`c_mem`) and lower than
   the batch's. Of the paper proof's invariants, Cfg and `W` are monotone the right way in the commit
   (a lower commit asks fewer witnesses, and `applied ≤ a ≤ commit` holds with `a = applied =` the
   snapshot index); only **I1** ("of two conf positions `p1 < p2` in a node's log, `p1 ≤ commit`")
   can fail. I1 of a node is used in exactly two places (section 3 and 4.1, 4.3 of the paper): to give
   the campaign record I2's "at most one conf entry above `k`" (which the far cases of sections 5
   and 7 contradict: "two conf entries above the commit, against I1 at `c`'s campaign"), and through
   I2 the new leader's I3(b). Every other use is of a leader's log (I3, the slices it sends), which
   comes from its campaign. The new clause checks that consequence at the campaign itself: the
   guard passes only when no conf entry is in `(applied, k]` and at most one is above `k`, which is
   I2. So I1 is no longer needed as an invariant of every node: the paper proof goes through with I1
   dropped at followers and I2 taken from the guard.
3. **No change in crash-free runs.** By I1 (which holds without crashes, and also when only a
   commit-only `HardState` is lost: the commit stored with the second change covers the first, the
   issue's "Cause"), the new clause never fires there.
4. **Term and vote.** The same cut loses the batch's term and vote too, with entries of a newer term
   kept. That is covered without the fix: nothing of the batch was acknowledged (etcd sends a
   follower's messages after `Save`), and the node's log with the newer term's entries beats every
   candidate of a lower term at the up-to-date check, while it cannot itself win a term below them
   (the voters that elected that term persisted their term before voting); this is the existing
   `raftState_crash` argument (`ApiCore.lean`'s item 1), now using the guard's at-most-one at the
   campaign instead of `confAboveOk` at the restart.
5. **Pre-vote.** The guard is checked at `hup`; a pre-candidate's log and commit do not change until
   its campaign (paper 4.1), so the check still holds when the pre-vote win turns into a campaign.

**Model check.** The repository's explicit-state checker (`notes/raft-conf-lag-model/checker`,
copied; a flag `-crashguard` adding the clause to the campaign guard, and `-crashinfer` for
section 4's variant), crash mode, `-n 4 -maxt 2 -maxlog 4 -maxconf 2 -maxval 1`, all invariants
(state machine safety, log matching, election safety, leader completeness):

| Bounds (crash mode) | Pinned guard | `-crashguard` (this fix) | `-crashinfer` (section 4) |
|---|---|---|---|
| `-n 3 -maxt 3 -maxlog 5 -maxconf 2 -maxval 1` | state machine safety violated (`elect 2 (2,3) 2`) | **exhaustive, no violation** (1.0·10^8 states, depth 45, 193 s) | exhaustive, no violation (1.07·10^8 states, depth 43, 196 s) |
| `-n 4 -maxt 2 -maxlog 4 -maxconf 2 -maxval 1` (the notes' `crash-sms`) | violated at depth 16 (as `trace-check-crash-sms.txt`) | no violation, depths up to 20 complete (4.6·10^8 states; table full at 21, not exhaustive) | no violation, depths up to 20 complete (4.6·10^8 states, not exhaustive) |

(The checker models the crash as a restart at the commit persisted before the last append, with
`applied = cfgidx = 0`, and checks no liveness. The checker copy, with the two flags, is at
`/home/ubuntu/.claude-E/jobs/b4c3a1d2/tmp/checker`; not committed.)

## 3. Liveness

The new clause fires only on a log with two or more conf changes above the commit index, which
(item 3 above) only such a crash leaves. The first of them is committed by the cluster (I1 of the
node's pre-crash state, `p1 ≤ c_mem`). The node may campaign again as soon as one of:

- it learns a commit index `≥ p1` (a `MsgApp` or heartbeat of any leader: heartbeats carry
  `min(match, committed)`) and applies through `p1`; then at most one conf change is above the
  commit and none unapplied below it. `TestRestartWithEntriesButNotCommit` checks this: after the
  partition heals node 1 applies both changes and wins a leadership transfer;
- a new leader truncates the entries above its commit (only uncommitted entries can be; `p1` is
  committed, so this concerns `p2` and later ones, after which the first bullet applies).

Not stuck forever, then, as long as some leader is elected. The residual cost: if every node able
to complete a quorum is in this state at once and no leader is left (for example a 3-voter cluster
whose leader is permanently gone while both followers each crashed inside such a `Save`), no one
campaigns, where the pinned code would elect (possibly unsafely, possibly safely). This needs a
crash inside the torn-write window on several nodes; for a process kill on etcd's WAL (a prefix of
the stream survives) the leader itself can never be in the state (it applied `p1`, so the state
record with commit `≥ p1` precedes its `p2` record).

**Scan cost.** The scan grows from `(applied, committed]` to `(applied, lastIndex]`: the extra
part is the uncommitted tail, in the unstable log (memory) and the `Storage` (for etcd a
`MemoryStorage`). It is paginated as before (`scan` with `pageSize = maxApplyingEntsSize`, i.e.
`MaxCommittedSizePerReady`, which `validate` defaults to `MaxSizePerMsg`; at 0 `limitSize` still
returns one entry per page) and stops at the first answer. A leader's uncommitted tail is bounded
by `MaxUncommittedEntriesSize` when set; a follower's by what leaders sent ahead of the commit. It
runs at `hup` only (an election timeout, `Campaign`, a `MsgTimeoutNow`), not per message or per
`Ready`. Under the flag the cost is the old one.

## 4. The alternative: infer the commit at a restart (`fix-plan.md` R1)

R1: in `newRaft`, after `loadState`, raise `committed` to the second-to-last conf change above it.
Sound under validation: a leader appends a conf change at `j` only when `pendingConfIndex ≤ applied`,
and `pendingConfIndex` is at least every earlier entry's index (`lastIndex` at `becomeLeader`, the
entry's own index at a proposal), so an earlier conf change in the same log (log matching: the
leader's log) was applied, hence committed. Implemented as a scratch variant (`raft-infer`, 42-line
patch, not committed): `go test ./...` passes except the tests that assert the pinned or the guard
behavior (`restarted with commit 1`); in the issue's execution node 1 restarts with commit 2,
applies `add 4`, and stays a pre-candidate in `{1,2,3,4}` (no split).

| | Guard (chosen) | Commit inference |
|---|---|---|
| Safety | Removes behaviors only; needs no protocol fact to be sound; closes the bug by checking I2 at the campaign | Adds a transition (a commit no leader announced); sound only if **every leader that wrote the log** enforced one pending change. A member running with `DisableConfChangeValidation` (or another implementation) while the restarting node has it off: the node applies an uncommitted entry, a state-machine divergence, worse than the bug |
| Liveness | Blocked until a leader informs it (section 3); a cluster-wide stall needs simultaneous torn writes on a quorum's worth of nodes with no leader left | Never blocked: the node applies `p1` and campaigns normally |
| Crash-free behavior | Unchanged | Unchanged |
| Upstream | A tightening of an existing safety check whose comment states the reason; maintainers already cite this guard (raft#234's closing) | A new protocol rule (commit learned from the log's shape, not from a leader); reviewers will ask for the global invariant it rests on, and it interacts with `DisableConfChangeValidation` and mixed configurations |
| Cost at runtime | Uncommitted tail scanned at each `hup` | Uncommitted tail scanned once in `newRaft` |
| Proof cost | `hasUnappliedConfChanges` and `CampaignGuard` change (one more disjunct, scan to `lastIndex`); I1 leaves the per-node durable invariant (kept for leaders, from the campaign); `raftState_crash` loses `confAboveOk`; **no new invariant** | `newRaft`/`RestartNode` change (the commit raised); a **new cluster-wide invariant** over every log in the system (durable logs, messages, leader logs): "an earlier conf change of a log is in the committed log", from the leader's `pendingConfIndex` check, so that the restart can show the raised commit is a prefix of the ghost committed log; `raftState_crash` loses `confAboveOk`. Larger (the plan's L) |

The guard wins on robustness (its failure mode is unavailability, the inference's is divergence),
upstream acceptability and proof cost; the inference wins only the corner liveness case. The two
compose (with the inference the guard's new clause never fires), so the inference can be added later
if that corner matters; it would bring the new invariant with it.

## 5. Tests (`commit_lost_with_entries_kept_test.go`, in the commit)

- `TestRestartWithEntriesButNotCommit`: the issue's test, adapted. Same execution up to the
  partition `{1, 2} | {3, 4, 5}`; then node 1's guard is true, `Campaign` leaves it a follower,
  and node 1 has no index 4; the partition heals, node 1 learns the commit index, applies through
  index 4 (`voters` five), its guard is false, and a `TransferLeader(1)` makes it leader; finally
  no index is committed differently on any node and node 3. Pinned code: fails (guard false at
  line 149; the issue's original version fails on the split as reported).
- `TestHasUnappliedConfChanges`: eleven restart-shaped logs (`MemoryStorage` with entries, a
  `HardState` commit and `Config.Applied`): one conf change above the commit allows; two (also
  `EntryConfChange` + `V2`) refuse; one in `(applied, committed]` refuses; the flag keeps the old
  answer. Pinned code fails 3 of 11 (the two-above rows).
- `TestCampaignWithUncommittedConfChange`: a 3-node cluster; the leader commits `add 4` and is cut
  off before its commit index reaches the followers; node 2 (holding the change uncommitted) wins
  and commits it. Passes on the pinned code; fails with the whole-log guard.

`go test ./...` (go1.27.3): all six packages pass, also with `-race`; `go vet ./...` clean. No
existing test's expectations change (none exercises two conf changes above a commit; the
interaction tests' outputs are unchanged).

## 6. Spec changes this brings (for the Lean stage)

- `SpecPlan/Spec/go_etcd_io/raft/v3/ApiCore.lean:248-255`: `CoreOpen.unappliedConf` gains the disjunct "at
  least two conf entries in `range (committed + 1) (lastIndex + 1)`" (the flag is off by
  `ConfigOk`, so the spec need not branch on it, but the proof reads the field); `CampaignGuard`'s
  docstring says so. `SpecPlan/Spec/go_etcd_io/raft/v3/raft__hasUnappliedConfChanges.lean`: the post is
  unchanged in form (`b = true ↔ o.unappliedConf`); the docstring's "scan of `(applied, committed]`"
  becomes `(applied, lastIndex]`; the premises (`us.snap = none`, `compactFloor ≤ applied`) still
  suffice (with no snapshot pending the entries above `applied` are in the storage or the unstable
  log). Its callers (`raft__campaign`, `raft__becomeCandidate`, `raft__becomePreCandidate`,
  `raft__Step`'s `hup`) take `CampaignGuard` as before.
- `SpecPlan/Spec/go_etcd_io/raft/v3/Api.lean:1024-1031`: `raftState_crash.spec` loses `D'.confAboveOk`; its
  docstring's "the condition on conf entries is what a restart needs ... open question" paragraph
  goes. `ApiCore.lean:83-87` (the realization, item 1): the term argument's "across at most one conf
  entry above its commit: `confAboveOk`" now reads it from the guard at the campaign.
- `SpecPlan/Spec/go_etcd_io/raft/v3/Model.lean:331-343`: `Durable.confAboveOk` deleted (its docstring is the
  bug report).
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/wal/Api.lean:252-278`: `Recs.confAboveOk` deleted;
  `Recs.crashScopeOk` keeps part (b) only (section 7), with its margin note (an at-rest lagging
  follower) gone; `crashInScope` stays as long as part (b) does. The WAL's crash laws (`:337-352`)
  unchanged in form.
- `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiBoot.lean:209-212, 233-247`: the boot's crash text
  loses "`R'.confAboveOk` gives `D'.confAboveOk`" and the paragraph on the bug; `raftNode__start.lean`
  step 6 and `NewServer.lean:63-67` (text only) follow; `notes/specs-only/top.md` K6's scope.
- The Lean proof (not on this branch): ConfI1 leaves the per-node durable invariant and stays a
  leader fact derived at `becomeLeader` from the campaign record; `hup`'s proof gets I2 from the
  guard's post.
- `etc/goose.py` project `raft`: pin the new commit once pushed; the translation of
  `hasUnappliedConfChanges` changes, nothing else. The issue file's `## Fix` then names the branch.

## 7. The snapshot part of `crashScopeOk`: a real crash state, not a bug

Part (b), "no snapshot record above the stored commit", is **not** a property of etcd's WAL
writes. At the pinned etcd (`a4d2bb172`), `raftNode.start` writes a received snapshot's WAL record
before the `Save` of its `Ready` (`server/etcdserver/raft.go:253-265`: `r.storage.SaveSnap(raftSnap)`
at 257, then `r.storage.Save(rd.HardState, rd.Entries)` at 264); `WAL.SaveSnapshot` encodes the
record and fsyncs (`server/storage/wal/wal.go:1089-1097`), while the state record that carries the
snapshot's commit (raft's `restore` sets `committed` to the snapshot's index, raft `log.go:468`) is
written later by `WAL.Save` (`wal.go:1055`, fsync at 1066). A crash in between leaves a durable
snapshot record above the last state record's commit. (The server's own snapshots cannot: they are
taken after `<-apply.notifyc`, `server.go:990`, i.e. after the `Save` of the state record with a
commit at least their index, which precedes them in the stream and which their fsync covers.)

It is **not a bug**: the restart ignores that record. `ValidSnapshotEntries` keeps only records at
or below the last state's commit (`wal.go:722-730`), `recoverSnapshot` opens the WAL at the newest
valid one (`bootstrap.go:451-462`), and `ReadAll` acts only on the start snapshot's record
(`wal.go:539-557`: other snapshot records are skipped), so the node restarts with its old log and
`HardState`, which is raft's "snapshot batch not written" case (`raftState_crash` covers a snapshot
batch with nothing of it written). The record stays in the WAL; it becomes valid only once a state
record with a commit at or above its index follows it, and by then the old entries above its index
written before it have all been overwritten by later records (the node's commit can pass the
snapshot's index only after a leader matched its log there, and the node's entries above its match
point, from before the snapshot, conflict with the leader's committed log), so a later restart at it
(`ReadAll` drops the entries before it above its index, `wal.go:548-550`) reads the same log as raft
holds. That last step is argued here, not tested.

So part (b) is a limitation of the WAL spec (`Recs.saveSnap` truncates the log at the record, as a
replay from that record does, while a restart before the next state record does not replay it), to
be closed in the spec (a snapshot record above the last state's commit is inert at a restart), not
by a fork change, and with no `issues/` or `nonissues/` entry.
