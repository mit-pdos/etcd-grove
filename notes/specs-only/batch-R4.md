# Batch R4: raft's tracker, quorum and confchange (report)

Author's report (2026-11-09). Wave 2. Packages `go.etcd.io/raft/v3/{quorum,tracker,confchange}`
(`.lake/src/raft/{quorum,tracker,confchange}/*.go`). New namespaces: `Quorum`, `Tracker`,
`ConfChange` (as `notes/specs-only/README.md` lists them).

## Files

All build (`etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3/{quorum,tracker,confchange}`: 8, 33,
24 modules).

- `Spec/go_etcd_io/raft/v3/quorum/Api.lean`: the pure quorum model, quorum's Go ownership
  (transparent), the `AckedIndexer` contract, the intersection laws.
- `Spec/go_etcd_io/raft/v3/quorum/`: 7 specs: `MajorityConfig__{CommittedIndex,VoteResult,Slice}`,
  `JointConfig__{CommittedIndex,VoteResult,IDs}`, `mapAckIndexer__AckedIndex` (internal).
- `Spec/go_etcd_io/raft/v3/tracker/Model.lean`: the pure model (`Membership`, `Valid`, `ProgressV`,
  `InflightsV`, the `Progress` transitions, `TrackerOk`, `Carried`). Imports nothing of raft's (R1's
  `Model.lean` is to import it).
- `Spec/go_etcd_io/raft/v3/tracker/Api.lean`: resources and laws.
- `Spec/go_etcd_io/raft/v3/tracker/`: 31 specs: `Config__Clone`, `MakeProgressTracker`,
  `ProgressTracker__{ConfState,IsSingleton,Committed,Visit,QuorumActive,VoterNodes,LearnerNodes,
  ResetVotes,RecordVote,TallyVotes}`, `matchAckIndexer__AckedIndex` (internal), `NewInflights`,
  `Inflights__{Clone,Add,grow,FreeLE,Full,Count,reset}` (`grow`, `reset` internal),
  `Progress__{ResetState,BecomeProbe,BecomeReplicate,BecomeSnapshot,SentEntries,CanBumpCommit,
  SentCommit,MaybeUpdate,MaybeDecrTo,IsPaused}`.
- `Spec/go_etcd_io/raft/v3/confchange/Model.lean`: the pure transitions (`simple`, `enterJoint`,
  `leaveJoint`, `changeV2`, `restore`, their steps), `Lists`.
- `Spec/go_etcd_io/raft/v3/confchange/Api.lean`: `ccsPts` (raftpb's, provisional), the result
  predicates, the internal working copy, the laws.
- `Spec/go_etcd_io/raft/v3/confchange/`: 22 specs: `Changer__{Simple,EnterJoint,LeaveJoint}`,
  `Restore`, and the internal `Changer__{apply,makeVoter,makeLearner,remove,initProgress,
  checkAndCopy,err}`, `chain`, `toConfChangeSingle`, `checkAndReturn`, `checkInvariants`, `joint`,
  `incoming`, `outgoing`, `outgoingPtr`, `nilAwareAdd`, `nilAwareDelete`, `symdiff`.
- `examples/specreq/raftconf/`: `quorum.go` (`ReqJointCommitted`, `ReqJointVote`, `ReqEmptyHalf`),
  `tracker.go` (`ReqCommittedQuorum`, `ReqTallyVotes`, `ReqVisitSorted`, `ReqInflightsFull`,
  `ReqProgressFlow`, `ReqCloneFresh`), `confchange.go` (`ReqApplyLikeRaft`, `ReqRestoreEmpty`,
  `ReqRestoreRoundTrip`, `ReqLastVoter`, `ReqJointCycle`). `go vet` and `gofmt` clean; all ran once
  without panicking (a throwaway test, not committed).

## Exported vocabulary

### `Quorum` (`quorum/Api.lean`)

Pure: `VotePending`/`VoteLost`/`VoteWon`; `sortMax` (`2^62`, Perennial's sort bound); `MajQ s q`
(`q` holds a strict majority of `s`; any set, of `∅`); `JointQ s0 s1 q`; `granted`/`rejected votes`;
`majVote`, `jointVote` (Go's `VoteResult`); `MajorityIdx s f N`, `JointIdx s0 s1 f N` (Go's
`CommittedIndex`, R3's relations); `sorted s`; `ackedFrom s f N`; `Adjacent a0 a1 b0 b1` (two joint
configurations one step apart).

Go ownership (transparent: the Go types themselves): `majorityOwn m dq s` (a `MajorityConfig` map or
`nil`); `jointConfigOwn c dq s0 s1` (R3's provisional predicate, same signature);
`isAckedIndexer l P acked` (the interface's contract, with the caller's resource `P`).

Laws: `isAckedIndexer_persistent`; `majQ_intersect` (two majorities of a non-empty set meet);
**`jointQ_intersect`** (quorums of `Adjacent` joint configurations meet: R2's safety);
`majorityIdx_quorum`, **`jointIdx_quorum`** (a quorum index is matched by a quorum);
`majorityIdx_mem`, `jointIdx_mem` (it is some voter's acknowledgement).

### `Tracker` (`tracker/Model.lean`, `tracker/Api.lean`)

Pure: `Membership` (R1's five fields, `simple`, `empty`, `ids`, `isJoint`); `Membership.CfgOk`
(`checkInvariants`); **`Membership.Valid`** (CfgOk, no id 0, voters unless empty, no staged learner
among the incoming voters); `PrState`; `InflightsV` (`size`, `maxBytes`, `items`; `bytes`, `full`,
`freeLE`, `empty`); `ProgressV` (`matched`, `next`, `sentCommit`, `state`, `pendingSnapshot`,
`recentActive`, `paused`, `isLearner`, `ins`; `isPaused`, `resetState`, `becomeProbe`,
`becomeReplicate`, `becomeSnapshot`, `sentEntries`, `canBumpCommit`, `maybeUpdate`, `maybeDecrTo`,
`fresh`); `TrackerOk m pv` (the map tracks exactly the ids, learners marked); `Carried pv m' li mi mb
pv'` (the map after a change); `inflightsMax` (`2^62`); `matchOf`, `activeIds`, `tallyCount`,
`Membership.quorum`, `ProgressV.toGo`, `TrackerV`.

Resources: `configOwn cfg dq m` (opaque: a `Config` value's maps hold `m`, canonical, `m` valid);
`inflightsOwn p I` (opaque); `progressValOwn pv P`, `progressOwn pr P` (transparent: the `Progress`
struct, its ring owned); `progressMapOwn mp prs pv`; `trackerOwn tv T`; `progressTracker t T`
(transparent: raft's `r.trk`).

Laws: `configOwn_valid`; **`configOwn_open`** (the `JointConfig` and the auto-leave flag, what raft
reads directly); `configOwn_fractional`; `configOwn_timeless`, `inflightsOwn_timeless`;
`inflightsOwn_size`.

### `ConfChange` (`confchange/Model.lean`, `confchange/Api.lean`)

Pure: `AddNode`/`RemoveNode`/`UpdateNode`/`AddLearnerNode`; `TransitionAuto`/`JointImplicit`/
`JointExplicit`; `Single`, `V2`; `remove`, `makeVoter`, `makeLearner`, `applyOne`, `applyAll`,
`apply`, `checked`, `symdiffTooBig`; **`simple`, `enterJoint`, `leaveJoint`, `changeV2`** (what
`raft.applyConfChange` does: R1's `Membership.applyChange`), `simpleEach`, **`restore`**, `Lists`
(R1's `ConfState.Is`).

Resources: `ccsPts sl dq cs` (raftpb's, provisional); `Base`, `BaseOf chg B`; `resultOk`, `changed B
r cfg trk err` (a `Changer` method's result), `result` (`Restore`'s); internal: `ccState`, `ccWork`,
`opSpec`.

Laws: **`changeV2_valid`**, `transitions_valid`; **`changeV2_adjacent`** (a change moves the voters
one step); **`changeV2_single`** (R1's `applyChange_v1`, corrected); **`restore_lists`** (a
`ConfState` listing a valid configuration restores to it), `restore_valid`; `simple_valid`;
internal: `ccState_done`, `ccState_abort`, `opSpec_persistent`.

## Main decisions and changes from the old specs

- **One configuration model shared with R1.** The old proof's `CfgM`/`CCState` (the configuration
  plus each tracked id's learner flag) is `Membership` alone: on every tracker raft builds the flags
  are the learner set (`TrackerOk`), so confchange's behavior is a function of the configuration.
  The model is exact at a valid configuration, with the Go error checks in order (and `Simple`'s
  `int` count wrapping, `symdiffTooBig`, so that the `Changer` specs need no size premise).
- **Errors as Go returns them.** `Changer.*` and `Restore` take any change and any `ConfState`
  (the old `Restore` took a premise that the model restores it): no error iff the model answers
  `some`, and then the new configuration; on error the tracker's progress map comes back
  (`changed`) or, for `Restore`/`chain`, nothing (raft panics, the examples drop it). Premises only
  where Go panics: a full ring in `Inflights.Add`/`SentEntries`, the snapshot state in
  `SentEntries`, a ring capacity past `inflightsMax`.
- **`Membership.Valid` defined** (R1 left it opaque) as exactly the configurations `Restore`
  round-trips, kept by every change; no size bound (the sort's `2^62` is a premise of the specs that
  sort: PRINCIPLES, "Keep a tool's temporary limitation as local as possible").
- **The progress values move with a change.** The old `ownResult` gave the new map's `Progress`
  copies with only their learner flags; the copies share the old `Progress`' rings, so the new
  `Carried` hands the values (old with the learner mark updated, or fresh) and consumes the
  tracker's map on success.
- **`Visit`'s footprint** is the `Progress` field and map at a share (was the whole tracker), so a
  callback can read `r.trk.Progress[id]` (raft's `bcastAppend`).
- **Results as the model's functions**: `VoteResult` is `jointVote`, `CommittedIndex` is `JointIdx`,
  `VoterNodes`/`LearnerNodes`/`Slice`/`ConfState` are sorted (were permutations), `TallyVotes`'
  counts stated (were free).
- **Quorum intersection across configurations** is a pure law (`Quorum.jointQ_intersect` over
  `Adjacent`, and `ConfChange.changeV2_adjacent`), which R2's safety argument cites.
- **Transparent where the Go type is the API**: `majorityOwn`, `jointConfigOwn` (Go maps of ids),
  `progressOwn` (raft reads and writes `Progress` fields directly), `progressTracker` (raft assigns
  `r.trk`, `r.trk.Config`, `r.trk.Progress`); opaque where a representation choice hides
  (`configOwn`: nil-ness and validity; `inflightsOwn`: the ring).

## Left out

- Logging/printing: `MajorityConfig.String`, `Describe`, `JointConfig.String`, `Describe`,
  `Index.String`, `VoteResult.String` (stringer), `Config.String`, `Progress.String`,
  `ProgressMap.String`, `StateType.String`, `confchange.Describe`. None had a spec before; none is
  used by a statement (raft's loggers format them only on paths `loggerOk` covers).
- Every function with an old spec has one (60 = 7 + 31 + 22).

## Open questions for the user

1. **The ring capacity bound** (`inflightsMax = 2^62`). `NewInflights` (every new peer, every term's
   `reset`) needs it: the ring's `int` index arithmetic would wrap above it, which Go cannot reach (a
   ring that large cannot be allocated) but Perennial's model can. Proposed: R1's `ConfigOk` adds
   `MaxInflightMsgs ≤ 2^62` (a scope restriction no client is near: etcd 4096). Alternative: a step
   or memory bound argument, which no spec has today.
2. **Where the sort bound comes from on raft's side.** Kept local (premises of `Visit`,
   `QuorumActive`, `VoterNodes`, `Committed`, `ConfState`, `CommittedIndex`), R2 must source
   `size ids ≤ 2^62` for its configurations: from the step bound (its open question 5), or else a
   bound in `Membership.Valid` with `changeV2` refusing a change past it (R1's first design: less
   local, and a refusal Go does not make).
3. **`Status().Config.AutoLeave`** is false in a joint configuration entered with auto-leave
   (`Config.Clone` drops it: `specs-ref`'s `issues/raft-config-clone-autoleave.md`, already filed).
   The spec states it (`{m with autoLeave := false}`); R1's `statusOwn` carries the clone.

## Findings for other batches

- **R1's `Membership.applyChange_v1.spec` is false** at the empty configuration (a node-0 or update
  change errs, "removed all voters") and for an unknown change type (an error, not a removal):
  `req/go_etcd_io_raft_v3.md`, "from R4", item 2; corrected as `ConfChange.changeV2_single.spec`.
- R1's `Membership.simple_valid.spec` has unneeded premises (non-empty, no local target, size).
- R2: a new peer's `Next` is `max(LastIndex, 1)`, not `LastIndex + 1`; the tracker's predicate,
  `Visit`'s footprint, the sort bound's source, `progressCopyOwn`'s definition: `req/…raft_v3.md`.
- R3: `jointConfigOwn`, `MajorityIdx`, `JointIdx` are now `Quorum`'s (same signatures).
- 3h: `ccsPts` (a `[]*ConfChangeSingle`, splittable per element), `confStatePts`, `ConfChangeV2`'s
  `LeaveJoint`/`EnterJoint` (panic on an unknown transition): `req/…raftpb.md`.

## Requirement hand-offs written

- `notes/specs-only/req/go_etcd_io_raft_v3.md`, "## from R4" (to R1: integration of `Membership`,
  `Valid`, `applyChange`; the false law; `ConfigOk`'s ring bound; to R2: the tracker in `raftCore`,
  `Visit`, the sort bound, the quorum laws, the `Changer` results, `progressCopyOwn`; to R3: quorum's
  predicates).
- `notes/specs-only/req/go_etcd_io_raft_v3_raftpb.md`, "## from R4".

## Integration: replacing R1's opaques

In R1's `Model.lean`: import `Spec.go_etcd_io.raft.v3.confchange.Model`; `abbrev Membership :=
Tracker.Membership` (delete R1's structure and its `simple`/`empty`/`ids`/`isJoint`, the same
definitions); `Membership.Valid := Tracker.Membership.Valid`;

```lean
def Membership.applyChange : ConfChangeI → Membership → Option Membership
  | .v1 cc, m => ConfChange.changeV2 ⟨ConfChange.TransitionAuto, [⟨cc.type, cc.nodeId⟩]⟩ m
  | .v2 c, m => ConfChange.changeV2 ⟨c.transition, c.changes.map (fun s => ⟨s.type, s.nodeId⟩)⟩ m
```

R1's laws then follow from R4's: `applyChange_valid` from `changeV2_valid`; `simple_valid` from
`ConfChange.simple_valid`; `applyChange_v1` (corrected) from `changeV2_single`. R1's `ConfState.Is`
is `ConfChange.Lists` of the five fields.

## Round 1 repairs (review `reviews/R4-review-1.md`)

- **F1** (`opSpec`'s `□` blocked `Restore`'s proof: its closures read the caller's `ConfState` and
  changes when `chain` runs them). `opSpec f F R` is no longer persistent (`chain` calls each op
  once) and threads a frame `R`, taken and given back; `chain.spec` takes `R` and gives it back on
  both exits. `Restore`'s sketch takes `R` = the `ConfState` share, the closures' variables and the
  ops' `ccsPts` (raftpb's per-element split, already requested). `opSpec_persistent` removed.
- **F2**: `Quorum.jointVote_won.spec` (won iff a joint quorum granted) and `jointVote_lost.spec`
  (lost iff some half's non-rejecters are no majority).
- **F3**: `ConfChange.changeV2_single.spec` is uniform at every valid non-joint configuration, the
  empty one included (bootstrap's `AddNode`s): `changeV2 ⟨Auto, [c]⟩ m = (applyOne c m).bind (fun m'
  => if m'.voters = ∅ then none else some m')`. R1's corrected `applyChange_v1` is its instance,
  with no voters premise.
- **F4**: `examples/specreq/raftconf/voters.go`: `ReqQuorumActive`, `ReqLearnerFlag`,
  `ReqVoterReads`, `ReqProgressCopy` (vetted, run once).
- Third tier: **N3** done (`Tracker.configOwn_agree.spec`). Not done: N1 (no raftpb vocabulary yet;
  `Restore`/`ConfState` keep R1's provisional `confStatePts` until integration), N2 (field-level
  footprints for the small tracker methods: no caller needs them), N4 (the ring bound stays a
  premise of `NewInflights`/`BaseOf`: open question 1). N5-N7 are R1's, or notes.
