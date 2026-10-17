# etcd-io/raft#168: "Extend Raft algorithm to support share witness"

- PR: https://github.com/etcd-io/raft/pull/168, head `43f19c68a57c2317805c76d90351c07327c89ffa`
  (two commits, Feb 2024, against `main` at `83d8deca0`; open, "needs rebase"). Design and
  background: etcd-io/raft#133 and the extended-Raft paper it links.
- Verified at: fork branch `pr-raft-168-goose-lean` (`~/etcd-pr/raft-168`, commit `9dbcc6487`),
  one commit on top of the pinned `raft37-goose-lean` (`509271dac`, raft v3.7.0 + the
  single-voter read-index fix); this branch `pr-verify/raft-168`.

## Verdict

**Not ready.** Within the part verified, the PR keeps raft's decisions unchanged for clusters
without a witness. Election is still decided by the same majority test: the new
`*VoteResultWithDifference`/`TallyVotesWithDifference` return `VoteResult`'s verdict, conjunct
for conjunct, and only add a count. The commit index is still `Committed()`; the new
`OneLessThanQuorum` only decides which entry is sent to the witness. Configuration changes are
proved to behave as before as long as no witness is involved.

For clusters **with** a witness, four of the PR's own code paths crash a node:
- restoring a joint configuration whose witness is in both halves (on restart, or when a snapshot
  is installed);
- a candidate whose log ends at a snapshot asking the witness for its vote;
- a leader whose "quorum − 1" index is compacted;
- (`OneLessThanQuorum` on a one-voter config, which raft itself can't reach.)

All four have Go reproductions at the PR head (below). Not covered at all: the raft package's
own changes (`stepCandidate`, `campaign`, `maybeCommit`, the subterm/replication-set logic,
`applyConfChange`'s new error) and `witness.go`, i.e. the extended-Raft algorithm itself. Its
safety argument (the witness's vote rule against the replication set) is not checked here.

## Scope

The PR changes or adds 76 Go functions (list below) across `raft`, `confchange`, `quorum`,
`tracker`, `raftpb`, plus a new `witness.go` and new protobuf fields. Far past the ~15-function
budget, so the subset verified is the one the coordinator asked for: **the quorum/joint and
tracker vote-counting and commit-index changes, and the `confchange` changes**, with their effect
on election and commit safety, plus the protobuf layer they need (the `raftpb` predicates and the
new getters). The raft package itself (`raft.go`, `rawnode.go`, `node.go`: `stepCandidate`,
`campaign`, `maybeCommit`, `appendEntry`, `becomeLeader`, `switchToConfig`, `applyConfChange`,
...) and `witness.go` were **not** re-verified: see "Callers not checked".

## Applying the PR (conflict resolutions)

The PR predates raft v3.7's move from gogoproto to protobuf-go v2 (pointer fields, getters), so
every file touching messages conflicted. Resolved in the base's style, without changing behaviour:

- `raftpb/raft.proto`: the PR's additions (`Entry.Subterm`, `WitnessHardState`,
  `ConfState.witness`/`witness_outgoing`, `ConfChangeAddWitness = 4`) without the gogoproto
  options; `raft.pb.go` **regenerated** (protoc 3.20.3, protoc-gen-go v1.36.11), not merged;
  `alias.go` gains `ConfChangeAddWitness`.
- **Zero left unset.** gogoproto's non-nullable `Subterm`, `Witness`, `WitnessOutgoing` have no
  presence (0 is absent). With pointer fields, `ProgressTracker.ConfState()` leaves
  `Witness`/`WitnessOutgoing` nil when 0, `appendEntry` sets `Subterm` only when non-zero (and
  clears a caller-supplied one, as the PR's assignment does), `MemoryStorage.Compact` copies it only
  when non-zero. Through the getters this is the PR's behaviour; it keeps witness-free
  `ConfState`s and entries byte-identical to v3.7's and `ConfState.Equivalent` (which
  `proto.Equal`s, presence included) working (with `new(0)` every restart panicked in
  `assertConfStatesEquivalent`: the first resolution failed `TestRestore` and the interaction tests).
- `quorum.MajorityConfig.OneLessThanQuorum` sorts with `slices.Sort` as the base's
  `CommittedIndex` does (the PR copied the then-current `insertionSort`); the PR's re-added
  `tracker.insertionSort` is dropped (unused). `ReplicationSet.String` uses `slices.Sort`.
- `witness.go` ported to pointer messages (`WitnessState.GetState()` returns
  `*raftpb.WitnessHardState`; fields through getters / `new(...)`).
- Tests: the PR's `_test.go` changes merged in the base's `require`/`assert` style; the
  datadriven `testdata/*.txt` regenerated with `-rewrite` (the same 22 files the PR changes,
  +1006/-439 lines vs the PR's +984/-465: the extra empty entries of the new subterms).
  `raftpb/raft_test.go`'s `ConfState` size is 160 bytes (two more pointers).
- `go build ./...`, `go vet ./...` and `go test ./...` pass in the fork worktree.

## Changed functions

State before = on `lean` (all of these packages are verified there: every function in
`etc/link-lean-first-raft.txt`). "Witness-free" = the old specification, re-proved with premises
that the configuration has no witness (below).

| function | kind | before | after | outcome |
|---|---|---|---|---|
| `quorum.MajorityConfig.VoteResultWithDifference` | new | — | verified | new spec: `VoteResult`'s verdict + `votesToWin` |
| `quorum.JointConfig.VoteResultWithDifference` | new | — | verified | new spec: `JointConfig.VoteResult`'s verdict + both halves' `votesToWin` |
| `quorum.MajorityConfig.OneLessThanQuorum` | new | — | verified, premise `|s| ≠ 1` | new spec; **panics on a one-voter config** (finding 4) |
| `tracker.ProgressTracker.TallyVotesWithDifference` | new | — | verified | new spec: `TallyVotes`'s verdict + `votesToWin` |
| `tracker.Config.Clone` | refactor (copies `Witnesses`) | verified | verified | old spec, witness-free |
| `tracker.ProgressTracker.ConfState` | behaviour (witness fields) | verified | verified | old spec, witness-free (fields nil) |
| `tracker.MakeProgressTracker` | refactor (`Epoch`) | verified | verified | old spec, unchanged proof |
| `tracker.ProgressTracker.{ResetReplicationSet, ChangeReplicationSet, OneLessThanQuorumInReplicationSet}`, `Epoch.*`, `ReplicationSet.*`, `scopedAckIndexer.AckedIndex` | new | — | translated | not specified |
| `confchange.Changer.initProgress` | behaviour (`isWitness` arg) | verified | verified | old spec at `isWitness = false` |
| `confchange.Changer.makeVoter` | behaviour (returns `error`) | verified | verified | old spec, returns `nil` (witness-free) |
| `confchange.Changer.makeLearner` | behaviour (returns `error`, clears `IsWitness`) | verified | verified | old spec, returns `nil` (witness-free) |
| `confchange.Changer.remove` | behaviour (clears `Witnesses[0]`) | verified | verified | old spec (no premise: a no-op on `[0,0]`) |
| `confchange.Changer.makeWitness` | new | — | translated | not specified (outside the witness-free scope) |
| `confchange.Changer.apply` | behaviour (`AddWitness`, errors) | verified | verified | old spec + premise "no `AddWitness` change" (incompatible: the old spec said type 4 is an error) |
| `confchange.Changer.Simple`, `EnterJoint` | behaviour (via `apply`; `EnterJoint` copies `Witnesses[0]` to `[1]`) | verified | verified | old spec + the same premise |
| `confchange.Changer.LeaveJoint` | behaviour (keeps the incoming witness) | verified | verified | old spec + premise `0 ∉ outgoing` |
| `confchange.checkInvariants` | behaviour (witness ⊆ voters check) | verified | verified | old spec, witness-free |
| `confchange.toConfChangeSingle` | behaviour (`AddWitness` for the witness) | verified | verified | old spec + premise "no voter `0`" |
| `confchange.Restore` | behaviour (via the above) | verified | verified | old spec + premises "no voter `0`, empty tracker witness-free"; **wrong for a joint config whose witness stays** (finding 1) |
| `raftpb.ConfState.GetWitness`, `GetWitnessOutgoing` | new (generated) | — | verified | new spec (field-level, returns 0) |
| `raftpb.ConfChangesFromString`, `ConfChangesToString` | behaviour (`'w'`) | not linked | translated | not specified |
| `raft.{appendEntry, applyConfChange, bcastHeartbeatWithCtx, becomeLeader, campaign, maybeCommit, maybeSendAppend, promotable, reset, switchToConfig}`, `stepCandidate`, `stepLeader`, `raft.poll` (renamed `pollAndReportDiff`) | behaviour | verified | not re-checked | — |
| `RawNode.{ApplyConfChange, Bootstrap, HasReady, acceptReady, readyWithoutAccept}`, `node.{ApplyConfChange, run}`, `newNode`, `MemoryStorage.Compact` | behaviour / API change | verified | not re-checked | — |
| `raft.{getWitnessVoteRequestReadiness, maybeStartNewSubterm, sendAppendToWitness, sendHeartbeatToWitness, sendRequestVoteToWitness}`, `raftLog.{entry, lastEntry}`, `witness.*` (11), `NewWitness`, `DescribeWitnessMessage` | new | — | translated | not specified |

## The specifications

New (files under `Spec/go_etcd_io/raft/v3/`):

- `quorum/MajorityConfig__VoteResultWithDifference.lean`: the verdict is
  `MajorityConfig.VoteResult`'s, conjunct for conjunct; the count is
  `votesToWin s votes` = 0 if the half has won (every election on the empty half is won) or can no
  longer win, else `|s|/2 + 1 − |granted ∩ s|` (≥ 1).
- `quorum/JointConfig__VoteResultWithDifference.lean`: `JointConfig.VoteResult`'s verdict
  (`MajQ` of both halves) and the array `[votesToWin s0, votesToWin s1]`.
- `tracker/ProgressTracker__TallyVotesWithDifference.lean`: `TallyVotes`'s verdict (`JQuorum`,
  `JLost`) at any configuration, and the two counts. **The PR does not change how an election is
  decided**: `stepCandidate` switches on the same verdict; the counts only decide when a witness is
  asked for its vote.
- `quorum/MajorityConfig__OneLessThanQuorum.lean`: for `|s| ≥ 2`, the largest value at least
  `|s|/2 = quorum − 1` voters reach (`IsCountIndex`), `MaxUint64` on the empty config; premise
  `|s| ≠ 1` (finding 4).

Changed: the confchange and tracker specs are the old ones on **witness-free** configurations.
The representation predicates say so (`InvConfchange.lean`: `ownCfgCC` has
`Witnesses = [0, 0]`, every `Progress` of a `Changer`'s result has `IsWitness = false`
(`ownNewPr`), the tracker it reads is witness-free (`ownTrackerCC`'s `NoWit`); `InvTracker.lean`:
`ownTracker` and `ownConfigV` have `Witnesses = [0, 0]`; `InvPb.lean`: `csPts` holds
`Witness`/`WitnessOutgoing` as cells of 0, `entPts` owns `Subterm` with its value unmodelled).
The new premises, each a place where the PR's code differs from the old on some input:

- `apply`, `Simple`, `EnterJoint`: no change of type 4 with a non-zero id. The old model rejects
  type 4 ("unexpected conf type"); the PR applies it. This is the intended behaviour change, and
  the one incompatibility: a caller relying on type 4 being rejected now gets a witness.
- `LeaveJoint`: `0 ∉ outgoing`. `isWitness := cfg.Witnesses[0] == id` is true for `id = 0` when
  there is no witness, so an outgoing voter 0 would now keep its `Progress`. Unreachable:
  `apply` skips `NodeId == 0`, so no configuration has a voter 0.
- `toConfChangeSingle`, `Restore`: no voter (or outgoing voter) `0`, for the same reason (a voter
  equal to `GetWitness() = 0` would be replayed as `AddWitness`).
- `initProgress`: `isWitness = false` (only `makeWitness` passes `true`).

## Callers not checked

Every raft-package function above calls these: `stepCandidate` → `pollAndReportDiff` →
`TallyVotesWithDifference`; `maybeCommit` → `OneLessThanQuorumInReplicationSet` →
`OneLessThanQuorum`; `switchToConfig`/`becomeLeader`/`stepLeader` → `maybeStartNewSubterm` →
`ResetReplicationSet`/`ChangeReplicationSet`; `applyConfChange` → `confchange.*`; `newRaft`/
`raft.restore` → `Restore`. Their proofs were not redone: `ownRaftPhys` does not own the new
`raft.witnessMsgs` or `trk.Epoch`, the `Progress` predicate does not record `IsWitness`, and
`Entry.Subterm` is unmodelled, so every one of them needs its spec extended first.

Building `Proof.go_etcd_io.raft.v3.Link` on this branch: 21 raft-package modules fail, and with
them everything downstream (`stepLeader`, `raft.Step`, `RawNode.*`, `node.*`, the protocol
results). The failing modules are `InvApplyConf`, `InvRawnodeReady`, `LemmasStepR`, `newRaft`,
`NewMemoryStorage`, `MemoryStorage.{Compact, ApplySnapshot}`,
`raft.{bcastHeartbeatWithCtx, maybeCommit, appendEntry, poll, promotable, becomeLeader,
switchToConfig, maybeSendAppend, reset, campaign}`, `stepCandidate`, `confChangeToMsg` and
`RawNode.{Propose, ReadIndex}`. Each one is a changed function, a caller of a renamed one
(`poll`), or a proof that builds a `ConfState`/`Entry`/`Config` literal that now has the new fields.
In particular the confchange premises (no `AddWitness`, no voter 0, witness-free tracker) are not
yet discharged at `raft.applyConfChange`, `newRaft` and `raft.restore`. That needs a raft-level
invariant "no voter 0, no witness", which `CCGood` does not carry today.

## Trust base

No axiom or `sorry` added. The new and re-proved results rest on what they rested on before
(`slices.Sort`, the protobuf-go trust boundary for the getters' callers).
`etc/tcb-report.py` could not run: it needs the whole tree built, and the raft Link does not
build. Instead, `#print axioms` of each new or re-proved `wp_proof` was checked (`TallyVotesWithDifference`,
both `VoteResultWithDifference`, `OneLessThanQuorum`, `Restore`, `LeaveJoint`, `checkInvariants`,
`ConfState`, `Config.Clone`). None depends on `sorryAx` or a proof axiom, only on the
type-level axioms of untranslated standard-library and protobuf types that every proof here
has. The callees enter as `wp_proof` hypotheses and are linked in the regenerated `Link.lean`.

## Findings in the PR

All reproductions are Go tests against the PR head (gogoproto `raftpb`; worktree
`43f19c68a`). The files, how to run them and their outputs are in `raft-168/` (`raft-168/README.md`). Each test fails there.

1. **`confchange.Restore` drops a witness that is in both halves of a joint configuration; a
   node then panics on restart or on installing a snapshot.** Severity: high, for any cluster
   with a witness that does a joint change keeping the witness (e.g. adding voter 4 to voters
   1 2 and witness 3 gives `(1 2 3 4)&&(1 2 3)`, witness 3 in both).
   - `toConfChangeSingle` replays the incoming half as "remove every outgoing voter, then add
     the incoming ones".
   - `remove(3)` deletes 3 from the incoming voters and clears `Witnesses[0]`, but keeps 3's
     `Progress`, because 3 is still an outgoing voter.
   - `makeWitness(3)` then finds an existing witness `Progress` and returns `nil` without adding
     3 back to the incoming voters or setting `Witnesses[0]`.
   - Result: the restored config is `(1 2 4)&&(1 2 3)` with witness 3 in the outgoing half only.
   - `newRaft` and `raft.restore` assert that the restored config equals the `ConfState`
     (`assertConfStatesEquivalent`), so the node panics.
   - Fix: in `makeWitness`, for an id already tracked as a witness, re-add it to the incoming
     voters and set `Witnesses[0]`, as `makeVoter` does for a known voter.
   - The proof here sidesteps this case by assuming a witness-free configuration; this test is
     the case outside that assumption.
```go
// confchange/witness_restore_test.go
package confchange

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

// A joint configuration in which the witness stays (here: adding voter 4 to
// voters 1 2 and witness 3) does not survive Restore of its own ConfState.
func TestWitnessRestoreJoint(t *testing.T) {
	chg := Changer{Tracker: tracker.MakeProgressTracker(10, 0), LastIndex: 10}
	cfg, trk, err := chg.Simple(pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeID: 1})
	must(t, err)
	chg.Tracker.Config, chg.Tracker.Progress = cfg, trk
	cfg, trk, err = chg.Simple(pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeID: 2})
	must(t, err)
	chg.Tracker.Config, chg.Tracker.Progress = cfg, trk
	cfg, trk, err = chg.Simple(pb.ConfChangeSingle{Type: pb.ConfChangeAddWitness, NodeID: 3})
	must(t, err)
	chg.Tracker.Config, chg.Tracker.Progress = cfg, trk
	cfg, trk, err = chg.EnterJoint(false, pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeID: 4})
	must(t, err)
	chg.Tracker.Config, chg.Tracker.Progress = cfg, trk
	cs := chg.Tracker.ConfState()
	t.Logf("live:     %s  ConfState %+v", chg.Tracker.Config, cs)

	cfg2, _, err := Restore(Changer{Tracker: tracker.MakeProgressTracker(10, 0), LastIndex: 10}, cs)
	must(t, err)
	t.Logf("restored: %s", cfg2)
	if cfg2.String() != chg.Tracker.Config.String() {
		t.Fatalf("Restore(ConfState()) differs from the live config:\n live     %s\n restored %s", chg.Tracker.Config, cfg2)
	}
}

func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}
```
```go
// witness_restart_test.go
package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// A node restarting while in the joint configuration (1 2 3 4)&&(1 2 3), with
// witness 3 in both halves, cannot restore its own ConfState: newRaft panics.
func TestWitnessRestartInJointConfig(t *testing.T) {
	cs := pb.ConfState{
		Voters: []uint64{1, 2, 3, 4}, VotersOutgoing: []uint64{1, 2, 3},
		Witness: 3, WitnessOutgoing: 3,
	}
	s := NewMemoryStorage()
	if err := s.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1, ConfState: cs}}); err != nil {
		t.Fatal(err)
	}
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("newRaft panicked on restart: %v", r)
		}
	}()
	newTestRaft(1, 10, 1, s)
}
```
2. **`raftLog.lastEntry()` panics when the log ends at a snapshot.** Severity: high (found by the
   reviewer).
   - `entry(lastIndex())` reads `entries(snapshotIndex)`, which returns `ErrCompacted`, and
     `entry` panics on it.
   - `sendRequestVoteToWitness` calls `lastEntry()`, so a candidate that has just installed a
     snapshot crashes as soon as it needs the witness's vote (in voters {1, 2, 3} with witness 3:
     self-vote, then one rejection).
   - Separately, `SnapshotMetadata` has no subterm, so even without the panic the candidate
     would report subterm 0.
3. **`maybeCommit` panics when the "quorum − 1" index is compacted.** Severity: high (found by the
   reviewer).
   - `r.raftLog.entry(wci)` panics if `wci < firstIndex()`. That happens when the (q−1)-th
     acknowledged index in the replication set is a follower that just received a snapshot, or one
     behind the leader's compaction.
   - It also loads the whole log tail on every `MsgAppResp`.
```go
// review_witness_test.go: reproductions of 2 and 3 (reviewer)
package raft

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func TestReviewLastEntryAfterSnapshot(t *testing.T) {
	s := NewMemoryStorage()
	cs := pb.ConfState{Voters: []uint64{1, 2, 3}, Witness: 3}
	if err := s.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1, ConfState: cs}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, s)
	defer func() {
		if x := recover(); x != nil {
			t.Fatalf("lastEntry panicked: %v", x)
		}
	}()
	_ = r.raftLog.lastEntry()
}

// candidate restored from a snapshot, gets 1 vote of 2 needed, asks the witness
func TestReviewCandidateAfterSnapshotWitness(t *testing.T) {
	s := NewMemoryStorage()
	cs := pb.ConfState{Voters: []uint64{1, 2, 3}, Witness: 3}
	if err := s.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1, ConfState: cs}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, s)
	defer func() {
		if x := recover(); x != nil {
			t.Fatalf("candidate panicked: %v", x)
		}
	}()
	r.Step(pb.Message{From: 1, To: 1, Type: pb.MsgHup})
	t.Logf("state %v term %d", r.state, r.Term)
	r.Step(pb.Message{From: 1, To: 1, Term: r.Term, Type: pb.MsgVoteResp})
	r.Step(pb.Message{From: 2, To: 1, Term: r.Term, Type: pb.MsgVoteResp, Reject: true})
	t.Logf("state %v witnessMsgs %d cfg %s votes %v", r.state, len(r.witnessMsgs), r.trk.Config, r.trk.Votes)
}

func TestReviewLeaderMaybeCommitCompacted(t *testing.T) {
	s := NewMemoryStorage()
	cs := pb.ConfState{Voters: []uint64{1, 2, 3, 4}, Witness: 4}
	if err := s.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: 10, Term: 1, ConfState: cs}}); err != nil {
		t.Fatal(err)
	}
	r := newTestRaft(1, 10, 1, s)
	r.becomeCandidate()
	r.becomeLeader()
	t.Logf("leader %v last %d first %d", r.state, r.raftLog.lastIndex(), r.raftLog.firstIndex())
	r.trk.Progress[3].RecentActive = false
	r.trk.Progress[2].RecentActive = true
	r.trk.Progress[4].RecentActive = true
	t.Logf("changed %v epoch %+v", r.trk.ChangeReplicationSet(), *r.trk.Epoch)
	r.trk.Progress[2].Match = 10
	defer func() {
		if x := recover(); x != nil {
			t.Fatalf("maybeCommit panicked: %v", x)
		}
	}()
	r.maybeCommit()
}
```
4. **`MajorityConfig.OneLessThanQuorum` panics on a one-voter config** (`pos = n - n/2 = 1` on a
   one-slot slice). Severity: low.
   - raft can't reach it: `OneLessThanQuorumInReplicationSet` calls it only when the half's
     witness is in the replication set, and that needs a non-witness voter excluded, so the half
     has at least 2 voters.
   - It is an exported `quorum` function, though; the spec here has the premise `|s| ≠ 1`.
```go
// quorum/witness_olq_test.go
package quorum

import "testing"

func TestOneLessThanQuorumSingleVoter(t *testing.T) {
	defer func() {
		if r := recover(); r != nil {
			t.Fatalf("OneLessThanQuorum of a one-voter config panicked: %v", r)
		}
	}()
	MajorityConfig{1: {}}.OneLessThanQuorum(mapAckIndexer{1: 5})
}
```
5. **Behaviour change for clusters without a witness.** Severity: low/medium.
   - The leader appends an empty entry on every configuration change it applies
     (`switchToConfig` → `maybeStartNewSubterm(false, true)`), and the subterm grows.
   - The log contents of a witness-free cluster therefore change: 22 datadriven test files are
     rewritten.
6. **`ApplyConfChange` returns `(nil, err)` instead of panicking** on an invalid change. Severity:
   medium (API change).
   - It is an incompatible public API change (`Node`, `RawNode`) for etcd and other users.
   - A caller that ignores the error now proceeds with a nil `ConfState`.
   - `RawNode.Bootstrap` drops the error.
7. Liveness and robustness only (from the reviewer):
   - `witness.processMessageWithOlderTerm` builds a `MsgAppResp` with no `Term`/`From`. raft drops
     it as a local message from node 0, so a stale leader is not told about the newer term.
   - `ChangeReplicationSet` picks the node to exclude by map iteration order (nondeterministic,
     no safety impact).
   - `ReplicationSet.Clone` drops `NonWitnessVoters` (it is unused).
   - `ConfState.Equivalent` normalises only `AutoLeave` before `proto.Equal`. A `ConfState`
     decoded with an explicit `witness: 0` would not equal the tracker's, which leaves the field
     unset. This only matters across the gogoproto/protobuf-go boundary, i.e. for this fork's
     resolution.
8. Open: the witness's vote rule (`handleVote`) checks the responders against the *incoming*
   replication set only, and counts rejections. The reviewer's argument that the incoming half
   alone protects committed entries looks right, but it is not proved here. The same goes for the
   cached witness state `processNoUpdate` answers from. Election and commit safety of the extended
   algorithm rest on these, and on the paper's proof, not on this work.

No bug was found in the existing (pinned) code, so `issues/` is unchanged.

## Reviewer

A fresh reviewer subagent checked the specs, the premises, the conflict resolutions and the
findings. Its conclusions:
- It confirmed findings 1 and 4, and added 2 and 3 (reproduced) and 5–8.
- It judged `votesToWin` and `IsCountIndex` right in every case.
- It judged the confchange premises sound but not yet discharged at the raft callers. The
  `0 ∉ outgoing`/no-voter-0 premises need a new raft-level invariant; `Restore`'s is stronger than
  needed, because `apply` skips `AddWitness(0)` just as it skips `AddNode(0)`.
- It found the nil-instead-of-pointer-to-0 resolution behaviour-preserving through the getters,
  with the `Equivalent` caveat (finding 7).
- Open: the `csPts` cells of 0 are an assumption that storage and snapshots carry no witness.

## Draft review comment

Thanks for the work on witness support. Reading the change against raft v3.7 (with the
protobuf-go v2 conflicts resolved), the vote counting and the commit index are unchanged for
clusters without a witness, and `Changer`'s behaviour is unchanged when no witness is involved.
With a witness, though, several paths crash a node:

1. `confchange.Restore` loses a witness that is in both halves of a joint config. Example:
   voters 1, 2 and witness 3, then add 4 jointly, giving `(1 2 3 4)&&(1 2 3)`.
   `toConfChangeSingle` removes all outgoing voters first. `remove(3)` keeps 3's Progress (3 is
   still outgoing), so the following `AddWitness 3` takes the "already a witness" early return in
   `makeWitness` and never re-adds 3 to the incoming config. `newRaft`/`raft.restore` then panic in
   `assertConfStatesEquivalent`, so a node restarting, or a follower installing a snapshot, in such
   a config crashes. A test is below. A fix: in `makeWitness`, for an existing witness Progress,
   still add the id to the incoming voters and set `Witnesses[0]`, like `makeVoter` does.
2. `raftLog.lastEntry()` panics (`ErrCompacted`) when the log ends at a snapshot, and
   `sendRequestVoteToWitness` calls it, so a candidate that just installed a snapshot crashes when
   it asks the witness for a vote.
3. `maybeCommit` calls `raftLog.entry(wci)`, which panics if the (quorum − 1) index is below
   `firstIndex()`, e.g. right after a follower received a snapshot. It also reads the whole log
   tail on every `MsgAppResp`.
4. `MajorityConfig.OneLessThanQuorum` indexes out of range for a single-voter config (`pos =
   n - n/2 = 1`). raft itself doesn't reach it, but it is exported.

Smaller points:
- The leader now appends an empty entry on every conf change even without a witness.
- `ApplyConfChange` changes signature and returns `(nil, err)`, and `Bootstrap` drops the error.
- The witness's stale-term `MsgAppResp` has no `Term`/`From`, so raft drops it.

Tests reproducing 1–4 are attached.
