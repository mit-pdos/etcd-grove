# R4 (raft's tracker, quorum, confchange): review, round 1 (provability and completeness)

Reviewer: one agent for both kinds, 2026-11-09, at `077835cb66` (R4's files unchanged since
`a43cf1d09d`). Read: `Spec/go_etcd_io/raft/v3/{quorum,tracker,confchange}/` (Model, Api, all 60
specs), `examples/specreq/raftconf/*.go`, R4's sections of `req/go_etcd_io_raft_v3{,_raftpb}.md`,
`batch-R4.md` (after my own pass), R1's `Model.lean`/`Api.lean` (configuration model and laws),
R3's `ApiLog.lean` (quorum predicates), `reviews/R2-provability-1.md` (b), the pinned Go
(`.lake/src/raft/{quorum,tracker,confchange}/*.go`, `raft.go`, `status.go`, `rawnode.go`,
`node.go`, `read_only.go`, `raftpb/confchange.go`), the Goose translations of `Restore`,
`JointConfig.CommittedIndex`, `Committed` and `applyConfChange`, etcd's server
(`.lake/src/server`) and `examples/raft/{kvreconf,kvdurable}`. I built nothing.

## What is good

- **The model is exact.** I checked every transition against the Go, step by step, at a valid
  configuration with `TrackerOk`: `remove`/`makeVoter`/`makeLearner` (`confchange.go:178-244`; the
  staged-learner case, the re-added-after-remove case, the `pr.IsLearner` early return, which is
  `id ∈ learners` exactly because the intermediate trackers keep "IsLearner iff in `Learners`", and
  outgoing voters are never learners); `applyOne`'s order (node 0 before the type switch,
  `UpdateNode` a no-op, an unknown type the error, `confchange.go:151-168`); `apply`'s final
  "removed all voters"; `simple` (joint refusal, `symdiff` against the tracker's original incoming
  map, `checkAndReturn`); `enterJoint` (joint refusal, zero-voter refusal, outgoing := incoming,
  then `apply`); `leaveJoint` (`confchange.go:103-118`); `changeV2` against `applyConfChange`
  (`raft.go:1958-1963`) and raftpb's `LeaveJoint()`/`EnterJoint()` (`raftpb/confchange.go:84-114`,
  the panic on an unknown transition); `restore` against `toConfChangeSingle`/`Restore`
  (`restore.go`). The quorum model too: `majVote` is `VoteResult` (`q = n/2+1 ≤ cnt` iff `n < 2cnt`;
  pending iff `|s \ rejected|` is a majority; the empty config wins); `MajorityIdx` is the value at
  `n - (n/2+1)` of the sorted, zero-padded acknowledgements (unique `N`); `jointVote`, `JointIdx`.
  The `Progress` transitions (`becomeProbe`'s `max`/`min`, `maybeDecrTo` in both states,
  `sentEntries`' `Next-1` index), `InflightsV.full` (wrapping byte sum), `freeLE` (= the loop's
  break) all match `progress.go`/`inflights.go`.
- **Errors as Go returns them.** `changed B (F m)` is the right shape: one spec over any change, the
  error disjunct exactly the model's `none`, the tracker's map back on error. The model being a
  function of the configuration alone (via `TrackerOk`) is what makes kvreconf's pre-check on a
  restored tracker agree with raft's tracker (different `LastIndex`, rings, progress).
- **Ownership is sound.** The `Changer`'s shallow copies share the tracker's `Inflights`
  (`confchange.go:341-345`), and the specs move the rings to the result and consume the tracker's
  map on success; on error the copies are dropped and the tracker's structs, never written, come
  back. `Restore`'s no-op case aliasing the tracker's own maps is covered by consuming `configOwn` at
  `own 1`. `Visit` at a share of the field and the map is exactly what `bcastAppend`/`switchToConfig`
  /`ReqVisitSorted` need. `progressOwn` transparent is right (raft writes fields and whole structs,
  `raft.go:813-821`).
- **Premises where Go panics, and the tool limits named and local**: `SentEntries` (snapshot state;
  a full ring in replicate), `Inflights.Add` (full), `sortMax` only on the sorting specs.
- **Snippets.** Thirteen, small, each reliance a `panic`; I could prove all but one dependency
  (below) from the specs.

## Answers to the brief's questions

**(a) The quorum laws are true, and one step is enough.**
- `jointQ_intersect`: `JointQ a0 a1 q1` gives `MajQ x q1`, `JointQ b0 b1 q2` gives `MajQ y q2`, for
  the `Adjacent` witnesses `x ≠ ∅`, `y ≠ ∅`, `|x Δ y| ≤ 1`. If `y = x ∪ {z}`, `|x| = n`:
  `|q1 ∩ x| ≥ ⌊n/2⌋+1`, `|q2 ∩ x| ≥ |q2 ∩ y| - 1 ≥ ⌊(n+1)/2⌋`, sum `≥ n+1`: they meet in `x`.
  `y = x \ {z}` is symmetric (`y ≠ ∅` is needed: `x = {z}`), `x = y` is `majQ_intersect`. True.
- `changeV2_adjacent`: leave: `x = y = m.voters` (non-empty: a valid joint `m` has ids, so voters);
  enter: `x = m.voters`, `y = m'.votersOutgoing = m.voters`; simple: `|V Δ V'| ≤ 1` once the `int`
  count does not wrap (the size premise), `V' ≠ ∅` by `apply`. True.
- `jointIdx_quorum`: `N ≤ N0`, so `ackedFrom s0 f N ⊇ ackedFrom s0 f N0`, a majority (or `s0 = ∅`).
  `majorityIdx_mem`/`jointIdx_mem` (with `f` = `getD 0`, as both specs instantiate it): true.
- Is one change enough for R2's restart-ahead case? Yes. R2-provability-1 (b) reduces it to a
  quorum of the candidate's own view `C_a`: the index it lacks was first committed under a view in
  `[f₀, f₁)`, which is `C_a` itself, so only the reflexive instance (`Adjacent a0 a1 a0 a1`, a
  non-empty half) is used; the commit-under-the-previous-view case (V3) is one `changeV2` step,
  `.skip` decisions are equal configurations, etcd's node-0 refusals are a reflexive step, and a
  node lagging several configurations is excluded by V2 and `hup`'s guard, not by a longer
  intersection (and is consistent with log matching: a candidate whose view is two steps on holds
  the conf entry, hence everything committed before it). `DisableConfChangeValidation` would break
  V2, but R1's `ConfigOk` fixes it off (`Api.lean:479`).

**(b)** Exact, as above, with one law statement too weak (F3).

**(c)** Sound, except the internal `opSpec` (F1), which makes `Restore`'s own proof plan fail.

**(d)** Premises: as above; `TrackerOk` is not a Go panic but the model's domain (every tracker
raft and the examples build has it); `inflightsMax` on `NewInflights`/`BaseOf` is a model limit
(open question 1, see N4).

**(e) R1's `Membership.applyChange_v1.spec` (`Api.lean:674-686`) is false, in both cases R4 says.**
- `m = Membership.empty` (valid under R4's definition, and it must be: `MakeProgressTracker`'s
  configuration, a joining node's), `cc.nodeId = 0` or `UpdateNode`: R1 says `some m`; Go's
  `Simple` runs `apply`, which skips the change and then returns "removed all voters"
  (`confchange.go:170-172`), so raft panics: `none`.
- `m = simple {1}`, `cc.type = 7`, `nodeId = 2`: R1's last branch is the removal, `m' = m`, valid,
  so `some m`; Go's `apply` returns "unexpected conf type" (`confchange.go:166-167`): `none`.
R4's `changeV2_single` fixes both (but see F3).

## First tier

### F1. `opSpec`'s `□` makes `Restore`'s proof plan impossible (confchange/Api.lean:123-130, Restore.lean, chain.lean)

`Restore`'s joint op is the closure `func(chg Changer) {... chg.EnterJoint(cs.GetAutoLeave(),
incoming...)}` (`restore.go`; Goose: `Code/go_etcd_io/raft/v3/confchange.lean:1879-1884`): it
loads the variable `cs` and calls `GetAutoLeave()` on the client's `ConfState` **when `chain` runs
it**, not when it is built. `chain.spec` takes each op as `opSpec f F`, which is `□ ∀ chg dq m B Φ,
… -∗ WP f chg {{Φ}}`: the closure's proof must read `*cs` from persistent resources only. But
`Restore.spec` holds the `ConfState` as `Raft.confStatePts csp dq csv` at the caller's `dq` and must
give it back; no persistent resource (no `inv`, no cancelable invariant: opening one needs a token
the `□` cannot hold) gives a read of it and returns the share. The Simple closures have the same
need for their `*ConfChangeSingle` (`ccsPts`), solvable only by discarding fresh ones, which needs a
persistence law raftpb's provisional `ccsPts` does not have (`req/…raftpb.md` item 1 asks for it;
nothing asks for `confStatePts`).

Who it affects: `Restore`'s own proof (the public `Restore.spec` is true; its sketch, "each an
`opSpec` … by `Changer.Simple.spec`/`EnterJoint.spec`; `chain`", does not go through), hence every
user of `Restore` (raft's `newRaft`/`appliedSnap`, the examples, five snippets).

Fix: thread a frame through the ops. `opSpec f F R := □ ∀ chg dq m B Φ, R ∗ configOwn … ∗ … -∗
▷ (∀ cfg trk err, R ∗ configOwn … ∗ changed B (F m) cfg trk err -∗ Φ …) -∗ WP …`, and `chain.spec`
takes `R` and gives it back on both exits (`R ∗ result B …`). `Restore`'s proof takes `R :=
confStatePts csp dq csv ∗ (the variables cs, incoming) ∗ ccsPts of the ops' elements`. (Or drop the
`□` and take each op once: `chain` calls each op exactly once, so `[∗list]` of non-persistent wands
is enough; then `opSpec_persistent` goes.) Ask raftpb (3h) for `ccsPts` split per element either way.

## Second tier

### F2. No law for what a won vote means (quorum/Api.lean)

R2's election safety needs `jointVote s0 s1 votes = VoteWon → JointQ s0 s1 (granted votes)` (from
`TallyVotes.spec`'s result at `raft.go:1715`); `ReqJointVote` and `ReqTallyVotes` also rely on it
(and on "a half that cannot reach a majority makes the vote lost"). Today a client gets it only by
unfolding `jointVote`/`majVote` and `w8` literal disequalities (`VoteWon ≠ VoteLost`). The README
keeps the model transparent but says "a fact the clients need is a law". Add
`jointVote_won.spec : jointVote s0 s1 v = VoteWon ↔ JointQ s0 s1 (granted v)` (the `↔` also serves
`QuorumActive`'s step-down), and optionally `jointVote_lost` (a non-empty half whose non-rejecters are
no majority).

### F3. `changeV2_single` has an unneeded premise and misses the bootstrap step (confchange/Api.lean:166-175)

`m.voters ≠ ∅` is only there because the stated right-hand side is wrong at the empty
configuration. The uniform statement is true at every valid non-joint `m`:

```lean
changeV2 ⟨TransitionAuto, [c]⟩ m =
  (applyOne c m).bind (fun m' => if m'.voters = ∅ then none else some m')
```

(one change: `symdiff ≤ 1`; `checked` passes: `CfgOk` is kept and `autoLeave` is already false).
It covers the case the current law leaves to an unfold: raft's `Bootstrap` applies `AddNode p` from
the empty configuration (`bootstrap.go`, `rn.raft.applyConfChange(cc.AsV2())`), which R1's
`StartNode`/`RawNode.Bootstrap` specs conclude as `Membership.simple (peers)` (`StartNode.lean:74`,
`RawNode__Bootstrap.lean:51`). With it, R1's corrected `applyChange_v1` is an instance with no
`voters ≠ ∅` premise, and etcd's uses are unchanged.

### F4. Completeness: three caller patterns without a snippet

- **`QuorumActive`** (`raft.go:1300`, CheckQuorum: the leader steps down iff the recently active
  voters are not a joint quorum): `QuorumActive.spec` is in no snippet (`ReqVisitSorted` covers only
  the `RecentActive` write after it). Add `ReqQuorumActive`: restore `{1,2,3}`, clear
  `RecentActive` of two peers through `Visit`, `QuorumActive()` must be false; set them back, true.
- **The learner flag as membership** (`raft.go:1992` `r.isLearner = ok && pr.IsLearner`;
  `promotable`, `raft.go:1948`; `node.go:395`/`rawnode.go:121`, an untracked sender): raft relies on
  "tracked and not `IsLearner`" meaning "a voter of either half", which comes from `TrackerOk` plus
  `Valid` (`learnersNext ⊆ votersOutgoing`). No snippet states it; add one after a `makeLearner` in a
  joint configuration (the staged learner is tracked, not a learner, and is an outgoing voter).
- **Direct voter reads** (`raft.go:2153` `r.trk.Voters[0][r.id]` with `IsSingleton()`;
  `raft.go:1063`, `2031` `Voters.IDs()[id]`; `raft.go:490` `VoterNodes()`): `IsSingleton.spec`,
  `JointConfig.IDs.spec`, `VoterNodes.spec` appear in no snippet. One snippet reading
  `trk.Voters[0][id]`, `trk.IsSingleton()` and `trk.Voters.IDs()` on a restored `{1}` and a joint
  configuration covers them. (Also uncovered, minor: `getProgressCopy`'s `Inflights.Clone`,
  `status.go:46-50`.)

## Third tier (preferences, notes)

- **N1. Coupling of two specs to R1's node API.** `Restore.lean` and
  `ProgressTracker__ConfState.lean` import `Spec.go_etcd_io.raft.v3.Api` (the whole node API) for
  `Raft.ConfState`/`Raft.confStatePts`, which are raftpb's (3h). Import the raftpb vocabulary once
  it exists (or R1's `Model` for the structure); otherwise every node-API change rebuilds them, and
  a future import of tracker's specs from R1's `Api` risks a cycle.
- **N2. Footprints of the tracker's small methods.** `RecordVote`, `ResetVotes`, `TallyVotes`,
  `IsSingleton`, `VoterNodes`, `LearnerNodes`, `ConfState`, `Committed` take the whole
  `progressTracker p T` (own 1). Raft holds it whole at each call, so no caller is blocked today; but
  `RecordVote`/`ResetVotes` touch only `Votes`, and `IsSingleton`/`VoterNodes`/`ConfState` only the
  configuration: field-level footprints (as `Visit` now has) would let a callback or a reader with a
  share call them. Not required.
- **N3. Missing agreement law** `configOwn cfg dq1 m1 ∗ configOwn cfg dq2 m2 ⊢ ⌜m1 = m2⌝`: the
  fractional law only recombines shares at one `m`. No user needs it today.
- **N4. Where the ring bound lives.** `BaseOf` asks `0 ≤ mi ≤ inflightsMax` at every `Changer`
  call and raft's `reset` asks it at `NewInflights(r.trk.MaxInflight, …)` (`raft.go:817`), so R2
  must carry it beside the tracker. Taking it once at `MakeProgressTracker` and carrying it in
  `trackerOwn` (PRINCIPLES, "a workload premise … on the resource's only producer, carried by the
  resource") would spare R2 that; `BaseOf` would still need it for a `Changer` built from a bare
  tracker value (the examples), so this is a choice, part of open question 1.
- **N5. `isLocalTarget` in R1's `simple_valid`.** R4 is right that `Valid` has nothing to do with
  it (confchange accepts any non-zero id, including `2^64-1`), but R1 should check whether some other
  statement of its needs "no member is a local target" (`node.go:395`, `rawnode.go:121` skip the
  unknown-sender check for local targets); if so it is a separate premise or invariant, not `Valid`.
  I found no Go bug there (uncertain: I did not trace a message from such a member through
  `rawnode.go`'s local-message handling).
- **N6. `ReqApplyLikeRaft`** is provable from R4's specs up to `validConf`'s `err == nil ⇒ changeV2 cc
  m = some m'` (with `restore_lists` for `m`); the last step, that this discharges R1's
  `RawNode.ApplyConfChange.spec`'s premise, depends on R1's statement and the integration of
  `applyChange := changeV2` (uncertain until R1 integrates).
- **N7.** etcd's server reads tracker values only through `Status()` (`server.go:1600-1615`,
  `isLearnerReady`: `rs.Progress[id].Match`): served if R1's `statusOwn` is stated over
  `progressValOwn` as R4's req item 5 proposes; nothing else of the server imports these packages.

## Snippet proofs (sketch)

- `ReqJointCommitted`: `JointConfig.CommittedIndex.spec` (the snippet's `acks` gives its own
  `isAckedIndexer` with `P = ownMap a`), `jointIdx_quorum` at `f = getD 0`: per non-empty half,
  `|half| < 2 |half ∩ ackedFrom|` and `n` counts exactly that set. ✓
- `ReqJointVote`, `ReqEmptyHalf`: unfold `jointVote`/`majVote` (F2), `MajorityIdx` unique,
  `JointIdx` with `s1 = ∅` gives `N1 = 2^64-1`, so `min = N0`. ✓
- `ReqCommittedQuorum`, `ReqTallyVotes`, `ReqVisitSorted`, `ReqInflightsFull`, `ReqProgressFlow`
  (each value checked against the model: `Next` 2, 4, 11, 11; `Count` 1), `ReqCloneFresh`: ✓.
- `ReqRestoreEmpty`, `ReqRestoreRoundTrip` (`restore_lists` twice; `sorted` is a function of the
  set, so `slices.Equal`), `ReqLastVoter`, `ReqJointCycle` (lengths 3/3, then 3/0 with `len(prs) =
  3` from `Carried`'s `TrackerOk`): ✓ given `Restore.spec`, whose own proof is blocked by F1.
- `ReqApplyLikeRaft`: see N6.

## Ranking by need of revision

1. **confchange**: F1 (first tier, internal but blocks `Restore`'s proof), F3, N1.
2. **quorum**: F2 (missing law R2 needs).
3. **tracker**: F4 (snippets), N2-N4.

## Verdict

The model is faithful to the Go code in every transition and error case I checked, the quorum
laws are true and are what R2's safety argument uses (one step is enough), the ownership story is
sound, and R4's correction of R1's `applyChange_v1` is right. One first-tier finding: the internal
`opSpec`'s persistence makes `Restore` unprovable as planned (a frame through `chain` fixes it).
Repair F1-F4; no second round is needed for the rest.
