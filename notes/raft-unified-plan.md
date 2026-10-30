# One raft mode with snapshots and reconfiguration, and `examples/kvreconf`'s adequacy

Started 2026-10-28 (branch `kv-snap-reconf`, then `raft-unified`). The user's request: specs, by the
spec skill, that cover reconfiguration and snapshots for raft in one proof; that proof; and, at the end,
the adequacy of `examples/kvreconf` (its `Main` never panics: porcupine answers Ok).

## Where it starts

- Raft's proof has two modes (`notes/STATUS.md`, D1): static (snapshots, fixed voters:
  `isStaticCluster γ N vs snapOk`) and dynamic (reconfiguration, no snapshots: `isDynamicCluster γ N c0
  decode`, `reNoSnap = true`, `storCap 1`). The protocol already handles a `MsgSnap` restored at a
  changing configuration (`raft.Step`, stage B8: `GMode.SnapDyn`, `StepR.snapRestore`); what is missing
  is above it (review 1, `notes/spec-first-study/raft-node-unified-review-1.md`, and the map of the
  modes in this file's "Machinery" below).
- `examples/kvreconf` (Go only): every choice of the application random (`notes/STATUS.md`).
- The raft it needs: the fork's `raft37-goose-lean-a2` (`565c2bd`, local in `.lake/raft-fork`, not
  pushed), which switches to a snapshot's configuration when it is applied
  (`issues/raft-snapshot-during-apply-stale-confchange.md`). The protocol model switches at restore
  (`StepR.snapRestore` sets `cfg`); it must follow the fix.

## The user's decisions (2026-10-28)

- The fork branch `raft37-goose-lean-a2` pushed; the raft pin moved to `565c2bd` (`etc/goose.py`,
  `examples/go.mod`, `examples/k8setcd3/go.mod`; `etc/goose.py --check --project raft` up to date).
- The trust-base fact `ccDecodeV2_nil` added
  (`Spec/google_golang_org/protobuf/proto/UnmarshalConfChangeV2Empty.lean`), for U5.
- The conf-change rule fixed at allocation (`γ.rule`) is replaced by a TaDa design: clients own, for
  each committed conf entry, a one-shot permission to decide it (apply a change or skip it), the
  decision recorded once in raft's ghost state; e.g. an implementation that agrees out of band on a
  random but unanimous decision. Redesign: the decisions section below (the frozen candidate's
  `ConfRule` parts superseded).

## The spec

Designed with the spec skill over eleven review rounds (`notes/spec-first-study/raft-node-unified-review-*.md`);
frozen as candidate 12 (`notes/spec-first-study/raft-node-unified-candidate.md`, the design the stages
implement; Tier 2-3 wording settles in the stages). Its shape:

- one parameterless `isCluster γ N`; the cluster's fixed choices projections of `γ`: `γ.c0` (the initial
  membership of a storage's `ConfState`), `γ.rule : ConfRule` (the application's decision for each
  committed conf entry: apply a change, or reject it without calling `ApplyConfChange`). The rule is
  fixed at allocation because the protocol folds it over every log prefix, uncommitted ones included
  (`DynCfg.fold`/`adj`);
- snapshots TaDa style: the client's `ownSnapsMade γ S` (making one takes and returns it), `snapMade γ s`
  for one out of raft, at a committed prefix with its configuration (`Membership.fold γ.rule γ.c0 l`);
- one allocation for `StartNode`'s bootstrap and `RestartNode` from `γ.c0`; `joinAuth`/`nodeJoin` for
  newcomers;
- `nodeConfig` for every node; laws past non-conf and rejected entries; `Advance` of a snapshot moves it;
  `ApplyConfChange` of any valid change (joint, automatic leave);
- one-shot proposal updates, with a client-owned registry of proposals so the client can pay for each
  copy the network or a retry commits; raft's automatic leave told by its position (`RaftLeave`); the
  transfer choice; no credits in the API;
- `CreateSnapshot` of any prefix the storage holds (`storHoldsLb`, from the append and from `Advance`),
  before `Advance`; today's atomic storage specs otherwise; a law for a storage wrapper; importable
  `confchange`/`tracker` specs (`ownTrackerM`);
- new specs: `Campaign`, `ForgetLeader`, `Status`, `Stop`.

## Stages

Each stage on its own branch off the previous one's head (integration: one integrator merges, builds,
pushes; `notes/` memory "integration train"); agents for the proof work, a small lemma module and a
commit per lemma.

- **U0. Pin.** Translate raft from `raft37-goose-lean-a2` (`etc/goose.py --src raft=.lake/raft-fork`;
  the pin moves once the fork branch is pushed: the user's approval); re-prove `raft.appliedSnap`,
  `raft.restore`, `raft.Step`'s `MsgSnap` case with the configuration switched at `appliedSnap`
  (`StepR.snapRestore` keeps `cfg`, `StepR.applySnap` switches it; `SnapCfgOut` moves to `appliedSnap`).
- **U1. Vocabulary.** `ConfRule`, `Membership.fold`, `ConfRule.validated`, the joint `applyChange`
  laws, the filler extension, `SnapRec`; their laws proved (pure).
- **U2. Dynamic snapshot certificates.** `snapshotCert_make`/`_made` over the dynamic clause of
  `raftSnapCert` (`D.fold fp = some k.cfgM`, `Protocol/Ghost.lean:1551`): define `SnapObl`; the
  client-owned `ownSnapsMade`.
- **U3. RawNode in one mode.** Lift `DynNoSnap` (`RawNode.Step` supplies `GMode.SnapDyn` from the
  message's certificate), the `"%Hsnap"` clause (a pending snapshot in the dynamic invariant), the
  `MsgStorageAppendResp`/`ApplyResp` snapshot cases (`StepR.applySnap`), `RNState.cfg/capplied`
  following a restore. (2026-10-28: U3a, the model, U3b, `raft.Step`'s two storage-response cases, and
  U3c, the `RawNode`, done; U3d, the node, done: `notes/decisions.md`, "Stages U2, U3", "Stage U3d".)
- **U4. Allocation without `reNoSnap`, joiners.** `ownRaftGhost_alloc_core` for a dynamic cluster with
  snapshots and an empty or bootstrap log; `joinAuth`; `RestartNode` from `γ.c0`; a joiner (empty log,
  configuration `c0`) in the protocol invariant beside the founders; pre-votes granted at term 0 with
  no `bootedCluster` premise (scope: newcomers start at `c0`, not on an empty `ConfState`).
  (2026-10-29: done in the decision cluster, empty bootstrap log: `notes/decisions.md`, "Stage U4:
  joiners"; spec changes below. A bootstrap-log allocation, and joiners there, remain.)
- **U5. Automatic leave.** `raft.appliedTo`'s leave proposal (its recursion into `r.Step`), so that
  `c.autoLeave → role ≠ leader` goes from `appliedTo`, `appliedSnap`, `raft.Step`; the invariant that a
  committed empty `EntryConfChangeV2` is raft's leave where the configuration is joint (`RaftLeave`, for
  `opsOf`); the trust-base fact `ccDecodeV2 [] = some` the empty change (the user's approval).
  (2026-10-29: done but for `committed_emptyV2_joint`: `notes/decisions.md`, "Stage U5: automatic
  leaves"; spec changes below. Later that day, track A: `committed_emptyV2_joint` and
  `committed_confDecodes` proved, `notes/decisions.md`, "Stage U5: the committed conf-entry laws".)
- **U6m. Rejection in the model.** The protocol's decoder a decision (`apply op | reject`); `entStep` of
  a rejection keeps the state (joint configurations included); `applyConf` and `advance` require "no
  undecided conf entry between".
- **U6. Rejection in the API.** `nodeConfig_reject`, `nodeConfig_skip`; `Advance` with every delivered
  conf entry applied or rejected.
- **U7. Messages.** The proposal registry (`ownProposals`, `proposalReg`, `sentMsg_prop`) and
  `msgCredits_intro` (a client-supplied update per copied `MsgProp` entry); `SentMsgShape` in every
  cluster (a re-forwarded `MsgTransferLeader` never reaches `send`'s `Panicf`); the transfer choice;
  raft's proofs take their own time receipts (no read or tick credits in the API).
- **U8. Storage.** `storHoldsLb` (a `StorageModel` field; laws from the append receipt and `Advance`) and
  the hold mark `storHoldMark` that `ApplySnapshot` respects (so `storHoldsLb` is persistent);
  `CreateSnapshot` over it with today's token, mask and resources, its term fixed in the post;
  `SetHardState` importable; the wrapper law.
- **U9a. Stopped nodes.** `nodeLive` (fractional, whole from `StartNode`/`RestartNode`), `Stop` taking it,
  `nodeStopped` with every stopped answer; each method's one triple with the stopped disjunct.
- **U9. The node specs.** One spec per function over `isCluster`; `Campaign`, `ForgetLeader`, `Status`,
  `Stop`; the static family and `dynamicSpec`s deleted; `interface/` regenerated; the unfold list of the
  clients emptied (laws).
- **U10. Clients.** etcd's server re-certifies its snapshots by `snapshotCert_make` (its free registry
  was valid only in the no-snapshot mode, `SnapTake.lean`; `ep.confState` may be `nil` after a stopped
  `ApplyConfChange`); kv (its Go may now snapshot after a conf change), the other examples
  over the unified API; `etc/tcb-report.py --check` unchanged but for approved changes.
- **U11. kvreconf.** Go made provable (the newcomer's `Storage` with `c0`'s `ConfState`, `Replica.cs`
  starting at it; bounded indices and sequence numbers, as kv's; no bound on ticks or campaigns: raft
  takes its own time receipts), a Goose project, the importable `confchange`/`tracker` specs over
  `ownTrackerM` and `validConf` over them, its specs and proofs, its `Main`'s adequacy
  (`kvreconf_porcupine_safe`).

## Spec changes during U4 (2026-10-29)

Each: old → new, and why.

- `stepIn_intro` (`InvNode.lean`): premise `⌜st.msg.Type' ≠ MsgPreVote⌝ ∨ bootedCluster γ` → none. A
  node at term `0` has an empty log (`ownStepGhost_term0`) and grants every pre-vote, so no rejection is
  sent at term `0`; the premise excluded pre-votes from every cluster started empty (the frozen design's
  E4). `bootedCluster`/`nodeBoot_booted` are kept (now unused by raft; their removal is U9's).
- `RawNode.Step.spec`: premise `st.msg.Type' = MsgPreVote → γ.reBoot ≠ []` → none (same reason).
- `cluster_alloc_dec` (`InvNodeRule.lean`): post adds `joinAuth γ (GMap.listToSet vs)` (the design's
  `joinAuth γ (founders)`).
- New: `joinAuth γ U`, `nodeJoin γ N id`, `joinAuth_join`. **Departure from the design's statement:**
  `joinAuth_join` takes `isCluster γ N` (a persistent premise: `isCluster γ N ∗ joinAuth γ U ==∗ joinAuth
  γ ({[id]} ∪ U) ∗ nodeJoin γ N id`). `joinAuth γ U` has no namespace, but the token is of the cluster in
  `N` (`isNode n γ N id` after `RestartNode`), so the law needs the cluster at `N`; every client holds it.
- `RestartNode.unifiedSpec`: premise `cv.ID' ∈ vs` → none (no node needs it in the dynamic mode, a
  founder included: raw `RestartNode`'s `γ.reCfg = …` and `cv.ID' ∈ csm.Voters'` are now
  static-only); `nodeFounder γ N vs cv.ID'` → `nodeFounder γ N vs cv.ID' ∨ (nodeJoin γ N cv.ID' ∗ confAt
  γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ⌜vs.Nodup⌝)`. A newcomer is told that `vs` are the initial
  membership's voters by `confAt` at `0` (`cluster_alloc_dec` gives it), as the design's `confStateIs cs
  γ.c0` (the cluster has no public `c0`); `vs.Nodup` because `NewRawNode` takes the `ConfState`'s list
  without repeats.

## Spec changes during U11's `confchange`/`tracker` specs (2026-10-29, branch `raft-unified-cc`)

The frozen design is candidate §4b (`notes/spec-first-study/raft-node-unified-candidate.md`). Each item gives
the design, what was done instead, and why. All sent to the coordinator and approved.

- `Membership.applyChange` is unchanged: other tracks' frozen statements rest on it. It does not become
  Go's `confchange` (the design's H2). Instead there is a new sealed `Membership.applyGo` (Go's
  `confchange`, no cut), with `Membership.applyChange_eq_applyGo : applyChange o m = (applyGo o m).filter
  (size ·.ids < 2^62)`, and the `Changer` apiSpecs are stated over `applyGo`.
- `confchange.Restore.apiSpec`: the premises `confStateIs c m ∧ m.WellFormed` were not enough. They gain
  `m.Restorable` (new, transparent: `W64 0 ∉ m.ids ∧ ∀ k ∈ m.learnersNext, k ∉ m.voters`). Without it the
  statement is false. Take `m = Membership.simple {0}`, which is `Valid`: `Restore` runs `Simple([AddNode
  0])`, `apply` skips id `0`, and the call fails with "removed all voters". Take also `m = ⟨{1}, {1}, ∅, {1},
  _⟩`, which is `Valid`: `Restore`'s `AddLearnerNode 1` takes 1 out of the incoming voters, and the call
  fails the same way. Laws: `Membership.restorable_empty`, `restorable_simple` (`0 ∉ vs`),
  `applyGo_restorable` and `applyChange_restorable` (from a `WellFormed` membership), and
  `confAt_restorable : confAt γ k m ⊢ ⌜m.Restorable⌝`. This last one is why internal `ModeDec`
  (`InvApiDec.lean`) records the initial membership's `Restorable`; `cluster_alloc_dec` proves it from
  `W64 0 ∉ vs`.
- The `Changer` apiSpecs take no `m.WellFormed` premise: `ownTrackerM trk (some m)` carries the reachable
  state (`CCGood`). They give back `ownTrackerM chg.Tracker' (some m)`, since the tracker is only read.
- `ownTrackerM trk none` holds the fresh progress map owned. `Restore`'s derivation makes it read-only,
  as the internal spec takes it.
- New: `Membership.applyGo_asV2`/`applyChange_asV2` (a `ConfChange` is its `asV2`), asked for by track C.

## Spec changes during track B (U8 storage, U11 confchange; 2026-10-29, branch `raft-unified-storage`)

Each: old → new, and why. Items 1-7 and the confchange items were sent to the coordinator and approved.

- `MemoryStorage.SetHardState.spec`: made importable (`etc/api/raft.txt`; `RaftLink.MemoryStorage.wp_SetHardState`),
  as designed (J5). Done.
- The `confchange`/`tracker` items: the section above ("Spec changes during U11's ...").
- (approved, in progress, WIP branch `raft-unified-storage-wip`) 1. `StorState.hd` (the hold, `0` for a fresh
  storage): the design's `storHoldMark` as a field of the owner's view. 2. `isStorageWith`: `HSnapshot`'s
  application snapshot `≤ σ.fl`, term over `σ.ents` → `≤ σ.hd`, term over `storApp σ σ.pend` (raft's goroutine
  may read a snapshot the client took mid-`Ready`); `PendAbove` stays the floor's, a new `HdAbove` (batch above
  the hold) in `Hhandout`'s premise; `Hfloor` raises the hold with the floor (`x ≤ h`). 3. `StorageModel`:
  `storTermsAt_intro`'s `≤ σ.fl` → `≤ σ.hd`; new `storTermsPre` (+ persistence, intro) and the receipt law
  `storTermsAt_receipt`; `storHoldsLb st l := ∃ ts, storTermsAt st ts ∗ ⌜l.map term <+: ts⌝` (a definition, in
  `NodeApiVocab`, with `storHoldsLb_mono`), `appendHold`/`appendHold_receipt` (`InvStorage`). kv's instance
  breaks (repaired at U10). 4. `MemoryStorage.ApplySnapshot.spec`: premise `σ.hd ≤ index`, post state
  `{memStorApplied sv with fl := σ.fl, hd := σ.hd}`. 5. `readyOut`/`snapReceipt`: the hold at most the snapshot's
  index (and at least the floor). 6. `MemoryStorage.CreateSnapshot.unifiedSpec`: `memFloorTok`/`i ≤ x` dropped,
  the hold-based `memTermsAt` gives `i ≤ hd` and the entry. 7. The design's `appendReceipt_holds` with an update
  (`|==>`). `MemoryStorage.Snapshot.spec`'s second disjunct as `HSnapshot`'s (done).
- (open) Where the hold is raised: `Hhandout` (first attempt) leaves raft a window
  (`notes/decisions.md`, "Track B"); the plan is a raise with the batch pending, after `acceptApplying`, which
  changes `Hhandout` back (no `h`, keeping `HdAbove`) and `Hfloor` (or a new law) to allow raising the hold alone
  while a batch is pending.
- (open) The storage-wrapper law (§4): not started.
## Spec changes during U5 (2026-10-29)

Each: old → new, and why. (a)-(e) sent to the coordinator and approved (the cross-track rule).

- (a) `opsOf l` (`NodeApiVocab`): `l.filter (!isFiller)` → `l.filter (!isFiller && !isEmptyV2)`, with the
  new `LogEntry.isEmptyV2 e := e.data = [] ∧ e.type = W32 2` and `opsOf_noType2`. As designed: raft's
  automatic leave (an empty `ConfChangeV2`) is no client operation. `isFiller` (and `isFiller_normal`)
  unchanged. Internal: the protocol's `Filler` is again `d = [] ∧ (ty = 0 ∨ ty = 2)`.
- (b) `node.ProposeConfChange.spec`'s update: `ownCommittedOps γ (ops ++ [⟨t, ty, bs⟩])` → `ownCommittedOps
  γ (ops ++ opsOf [⟨t, ty, bs⟩])` (the design's). An explicit `ConfChangeV2{}` is a filler (no deposit,
  `ccPropArg`'s filler case), so its update may not fire.
- (c) `node.ApplyConfChange.unifiedSpec` and `.dynamicSpec`: premise `m'.autoLeave = false` → none.
  Internal: `DynCCPreOp` loses `cs'.cfg.autoLeave = false`; `ownRawNode` (and `ownRawNodeReady`/`Idle`)
  lose the field `cf.autoLeave = false`.
- (d) `node.Advance.unifiedSpec`: `l.snap...AutoLeave' = false ∧ l.dlv.length = …` → `l.dlv.length = …`.
  Internal: `advanceP`'s and `runCfgLoan`'s auto-leave facts, `node.Advance.specRaw`'s premise gone.
- (e) `RawNode.Advance.spec`: premise `∀ l, rs.slent = some l → rs.mode.isDyn → …AutoLeave' = false` →
  none.
- Raft-internal: `raft.appliedTo.spec`: premise `c.autoLeave = true → s.role ≠ .leader` → at a leader
  `NStateWf s`, `s.term ≠ 0`, the last index a word, and a receipt `⧖ k0` in the pre; post `RET #()`
  at `logAppliedTo` → `∃ s' B recv, … ⌜LeaveStep c id s1 s' B recv⌝ ∗ (⌜last < B⌝ -∗ ⧖ (k0+1))`; stated
  at `HasLC.hasLC` (was generic `hlc`), as `raft.appliedSnap.spec` is now too (it calls it).
  `raft.Step.spec`: premise `m.Type' = MsgStorageApplyResp → c.autoLeave = true → s.role ≠ .leader` →
  none (its post unchanged). `StepProof.wp_Step_MsgProp` takes four callee specs, not
  `raft.Step.Postulates`, and its post gives `s'.logst.applied = s.logst.applied`.
- Not changed, though now unneeded upstream of `ownRawNode`: `csm.AutoLeave' = false` premises of
  `NewRawNode`, `StartNode`, `RestartNode`, `setupNode`, `newRaft` (starting at an auto-leave joint
  `ConfState`); left for U9 (`newRaft`'s tracker invariant still uses it).

## Spec changes during track A (2026-10-29)

Each: old → new, and why. New laws (no old text): `committed_confDecodes`, `committed_emptyV2_joint`
(`InvNodeRule.lean`), as the frozen design states them (`raft-node-unified-candidate.md`:170,
`raft-decisions-spec.md`:87; `committed_emptyV2_joint` takes the cluster's `N` explicitly, as
`confPolicy_decide` does). Raft-internal (no other track uses them):

- `isCommittedLogLb` (`InvApi.lean`, sealed): adds `cmtFactsS γ l` (raft's per-entry facts:
  `CCDecodes`, `ev2At`) beside the receipts' bound; `apiInvBody` adds `cmtFacts γ L`. Why: the two
  laws are pure entailments, so the facts must ride on the client's lower bound.
- `noopAu` (`GhostState.lean`): its commit also gives `ev2At γ L e` (in the dynamic mode, with no empty
  `ConfChangeV2` in the bootstrap log, an empty `ConfChangeV2` filler folds after `L` to a joint
  configuration over some recorded decisions); `noopAu_fire` takes it. **Breaks etcd's server**
  (`NewServerAlloc.lean`, `Spec/.../NewServer.lean` build a `noopAu`), already broken.
- `isEntryR` (`Ghost.lean`): its leader arm adds `ev2Rec γ e pt` (the entry's prefix, with the cores
  of its records `logRecsC`, folds to a joint configuration); the old body is `isEntryC`.
- `ownRaftGhost_step_propose` (`Refinement.lean`): one premise more (the batch's empty
  `ConfChangeV2`s at a joint configuration of the full log before them).
- `StepR.propose` (`StepR.lean`): premise `CCLeaveOk m.entries cs` added (the loop's decoded change
  of an empty `ConfChangeV2` wants to leave: `ccDecodeV2_nil`).
- `stepLeader`'s `LeaderProposeResult` (`Spec/go_etcd_io/raft/v3/stepLeader.lean`): `∃ cs, CCTypesOk
  ents cs ∧ …` → `∃ cs, CCTypesOk ents cs ∧ CCLeaveOk ents cs ∧ …` (proved from `ccEntsOk`,
  `ccEntsOk_leaveOk`; `stepLeader`'s proof now rests on `ccDecodeV2_nil` too).
- `UniNames` (`InvApiDec.lean`, behind `isCluster`): adds `∀ x ∈ γ.raft.reBoot, ¬ IsEmptyV2 x` (the
  decision cluster's bootstrap log is empty).

## Spec changes during track A, U7 and U9a (2026-10-29)

Each: old → new, and why. Approved by the coordinator where marked (the cross-track rule).

- `node.Tick.spec`: pre `isNode n γ N id ∗ tickCredit γ 1` → `isNode n γ N id` (the frozen text). Raft
  takes the tick's time receipt from a Go step of `Tick`'s own (`node__Tick.lean`, at a
  `StructFieldRef`); the old `tickCredit` stays (still exported) until U9.
- `stepIn_intro` (`InvNode.lean`): premise `tickCredit γ (if MsgTimeoutNow then 1 else 0)` → none (the
  frozen text's credit-free form). Internal: the API's `stepIn γ N id ml` is now `⌜ml ≠ null⌝ ∗ ∀ γn,
  ⌜NodeOk γ γn⌝ -∗ ⧗ 1 -∗ stepP γn id ml`, and `node.Step`'s raw spec takes `⌜ml ≠ null⌝ ∗ (⧗ 1 -∗
  stepP …)`, its proof taking the receipt at the `nil` check's comparison. The `NetMsgOk` / `≠
  MsgTransferLeader` premises stay until `SentMsgShape` lands (below).
- **Parked by the coordinator (the user is reconsidering it):** the proposal registry (`ownProposals`,
  `proposalReg`, `proposals_register`/`_elem`/`_all`, `Propose` taking `proposalReg`, `sentMsg_prop`,
  `msgCredits_intro` for `MsgProp`). Approved shapes before the hold: `cluster_alloc_dec` giving
  `ownProposals γ ∅`; one `node.Propose.spec` with `proposalReg γ data`, the old allocations giving `□ ∀
  d, proposalReg γ d`; `sentMsg_prop`'s normal disjunct `⌜e.Type' = W32 0⌝ ∗ (⌜e.Data' = []⌝ ∨
  proposalReg γ e.Data')` (an empty normal entry is a filler, with no registry key); `msgCredits_intro`'s
  per-entry update committing `ops ++ opsOf [entry]` (a filler's update is then the identity). Work in
  progress, checked in `InvApi.lean` but not committed: the ref `refs/wip/trackA-registry`
  (`2b5e6ebaf8`; `Cluster.pr`/`prAll`, the laws, `keyOk` in `freshOk`, `api_key_register` taking
  `keyOk`, `Protocol/Facts.lean`'s `deposited_fresh`).
- U9a, decided by the coordinator: (A) `node.ApplyConfChange`'s stopped disjunct is `⌜csp = null⌝ ∗
  nodeStopped n γ N`, without the frozen `nodeConfig v` (after `confc <- cc` the driver's view is with
  `run`, and the second select's `done` arm, unreachable, would need a sent/answered accounting to
  refute); `node.Advance`'s post is the running post ∨ `nodeStopped ∗ nodeDriver {handling := none}` (no
  storage facts: raft's `Advance` never ran). (B) K9's `P ∨ nodeStopped` preconditions are **not
  provided**: kvreconf's `Replica.stop()` waits for its loop and ticker before `node.Stop`, so no client
  calls a method holding only `nodeStopped`. A later client wanting them needs a send arm (`confc`,
  `advancec`, `propc`, `recvc`) shown never to commit once `run` is dead: `run`'s receive obligation on
  each channel a fraction of the liveness token, each fraction lent out returned to a "fraction bank"
  invariant at once (so that `run` reassembles the whole token at `Stop`), and handshake-lemma variants
  for the five channels.

- **The user's decisions (2026-10-29), changing the frozen design:** (1) no transfer choice
  (`transferChoice`/`transferAllowed`/`noTransfer` dropped, no mode): `node.TransferLeadership.spec`
  takes only `isNode` (and the context), `SentMsgShape` holds in every cluster (the `MsgTransferLeader`
  and `MsgTimeoutNow` shapes included), and `stepIn_intro` admits every sent message;
  `leaderTransferOn/Off` go with the old families in U9; the server's repair handles the new shapes.
  (2) (Corrected, confirmed by the user the same day.) `node.Stop.spec` takes the whole fractional
  `nodeRunning n γ N 1` (the frozen `nodeLive`, renamed) and gives `nodeStopped n γ N`; the law
  `nodeRunning_stopped : isCluster γ N ∗ nodeRunning n γ N q ∗ nodeStopped n γ N ⊢ False` lets a
  holder of a fraction refute every stopped answer. (An intermediate decision, `Stop` taking
  `nodeDriver`, was withdrawn.) (3) The proposal registry (S1, `Propose`) is not frozen yet.
- U9a as built (2026-10-29): `NodeNames.live` (a `dghostVar` of `Bool`: `false` in halves, the
  client's `nodeLiveRaw γ 1` and `run`'s; `true`, discarded, `nodeStoppedRaw`); `done` is Perennial's
  broadcast idiom with `Q := nodeStoppedRaw` (`isNodeChan`'s `ownBroadcastChan … .Unknown`, `run`'s
  `.Pending` in `runPre`); `stop` carries `nodeLiveRaw γ 1`. The names agree through the table:
  `CfgNames`/`cfgNamesOf` gained `live`, so `nodeRunning` (sealed, `InvApi.nodeRunning`: `NodeOk`,
  `isDyn`, `isNodeChan`, `nodeTabOk`, `nodeLiveRaw`) exists only in a dynamic cluster
  (`StartNode.dynamicSpec`, `RestartNode.unifiedSpec`; the static `StartNode.spec`/`RestartNode.spec`
  give none, temporary until U9), and `nodeStopped` is `∃ γn id, NodeOk ∗ isNodeChan ∗ (⌜static⌝ ∨
  nodeTabOk) ∗ nodeStoppedRaw` (the static disjunct the weak form). `nodeRunning_stopped`'s
  `isCluster` premise is unused by its proof (`nodeRunning` carries `isDyn`). `node.ForgetLeader.spec`
  is over `isNode` (its old triple the private `specRaw`). Not done: `node.Status.spec` (a False
  `status` handshake refutes `run`'s receive but not `Status`'s send, which needs the payload up front;
  `run`'s status arm needs `getStatus`'s spec: `getBasicStatus`, `getProgressCopy`'s `Visit`,
  `Config.Clone`); `node.Campaign.spec` (`MsgHup` is not in `netStepTypes`, so `netP_local` does not
  admit it; and `run`'s `r.Step(MsgHup)` raises the term by one, `raft.Step`'s `uint.Z s'.term ≤ uint.Z
  s.term + 1`, which `netP`'s `termLB` ceiling does not cover: a hup needs a budget step like a
  tick's, `budget_spend` with a time receipt. Admitting it through `NetMsgOk`/`netStepTypes` would
  change `stepIn`, a public vocabulary; a separate local case of `netP`, internal, would not).
- S1 as built (2026-10-29; candidate 15 rev 2, `spec-first-study/raft-propose-dup-spec.md`, as
  frozen): `RaftNames.dup : Bool := false` (`Protocol/Ghost.lean`), `Cluster.dup γ := γ.raft.dup`
  (`InvNode.lean`, sealed); `cluster_alloc_dec` takes `dup` and gives `⌜γ.dup = dup⌝`
  (`ownRaftGhost_alloc_core_reg` takes it; `ownRaftGhost_alloc_core` passes `false`);
  `node.Propose.spec`/`node.ProposeConfChange.spec` wrap the update in `□?γ.dup`; `msgCredits_copy`.
  `msgCredits_none`/`_snapshot` kept. Departures and details: (a) `cluster_alloc_static` also gives
  `⌜γ.dup = false⌝` (the frozen text names two old allocations; F2's every-allocation rule covers this
  third one, still exported). (b) The ticket's split is on its ghost variable's fraction: `propTk`'s
  `dghostVar γt (if γ.dup then □ else 1) none`, and `propIdx` gains the disjunct `⌜γ.dup = true⌝ ∗
  dghostVar γt □ none` (the ticket kept), instead of a bare persistent witness: the bootstrap
  entries' deposits are fired (`some i`, `boot_register`), and `fire_one`'s dup case still refutes a
  fired deposit by `none`/`some i` agreement. `entDataIs` is textually unchanged (its ticket part is
  `propIdx`). (c) `depSlot`'s unfired disjunct holds `□?γ.dup propAu1` (the deposited update), so
  `prop_deposit`, `propArg` (`InvNodeChan.lean`) and `ccPropArg` (`ApiVocab.lean`) take `□?γ.dup
  propAu1`; `api_propAu1_if` (`InvApi.lean`) lifts `api_propAu1`. (d) `nodeRunning_stopped`: isCluster
  premise dropped (unused). Not repaired (raft first): etcd's server (`NewServerAlloc*`, the
  allocation's post; `NodeBridge`, `Propose`'s `□?γ.dup`) and `examples/kv`.
- A standing rule from the user: any new ghost state (predicate, token, authority, witness) in a
  public spec is escalated before it is built on; never a minor change.

## Spec changes during track A (fresh) (2026-10-29)

Each: old → new, and why. (The second track A agent, from the hand-off below.)

- New: `node.Campaign.spec` (`Spec/go_etcd_io/raft/v3/node__Campaign.lean`), modeled on
  `node.ForgetLeader.spec`: pre `isPkgInit ∗ isNode n γ N id ∗ nodeCtx ctx cd`, post `nodeErr cd err`.
  No existing public statement changed, no new public vocabulary (the coordinator's option 1).
  Internal (raft-only): `netP γ id ml` (`InvNodeChan.lean`) is now `(old body) ∨ hupP γ ml`, with
  `hupSt` (the literal `pb.Message{Type: MsgHup}`) and `hupP γ ml := msgIn ml □ hupSt ∗ tickCred γ.bud
  1`; new `netP_hup`, `netP_split` (`stepWithWaitOption` reads the type through it). `run`'s `recvc`
  arm steps a hup with `wp_rn_raft_Step_hup` (`InvNodeRunHup.lean`, `RawNode.Campaign`'s proof with the
  message given), after `budget_spend` of the credit raises the term ceiling (as the tick arm).
  `Campaign` takes the credit from its own `MsgHup.Enum()` resolution (`wp_take_receipt`).
  `NetMsgOk`/`netStepTypes`/`stepIn` unchanged.
- New: `node.Status.spec` (`Spec/go_etcd_io/raft/v3/node__Status.lean`): pre `isPkgInit ∗ isNode n γ N id`,
  post `(st : Status), RET #st; statusOwn st`. **New public predicate** (escalated, approved as (A) by
  the coordinator): `statusOwn st` (`InvNode.lean`, sealed; `InvStatus.statusOwnRaw`), heap ownership
  only: `⌜st = zero_val Status⌝` (a stopped node's `Status{}`) ∨ `(∃ hs, hsRO HardState hs) ∗ (∃ c,
  ownCfgCC Config 1 c) ∗ (⌜Progress = nil⌝ ∨ progCopyOwn Progress)` (the nil disjunct, approved: a
  non-leader's map is `nil`, which `↦$` cannot own). No laws yet (track C asks when kvreconf's `Dump`
  needs them). The copy's `AutoLeave` is always `false` (`Config.Clone` drops it,
  `issues/raft-config-clone-autoleave.md`). Internal: `status`'s handshake predicate `fun _ => False` →
  `statusChP c := ∃ γc, isHandshake γc c statusOwnRaw True` (`InvNodeChan.lean`; one line each in
  `StartNode.lean`/`RestartNode.lean`, approved); `run`'s status arm answers with `getStatus`, so
  `node.run.wp_proof` takes `getStatus.spec` (last hypothesis). New internal specs and proofs:
  `getProgressCopy.spec` (`Visit` with the copy as invariant, `Inflights.Clone`), `getStatus.spec`
  (`getBasicStatus`, `getProgressCopy` at a leader, `Config.Clone` through the tracker's `Config`
  field); `Pos.Countable` instances for `SoftState`, `BasicStatus`, `tracker.Config`, `Status`.

## Spec changes during track A (third) (2026-10-29)

Each: old → new, and why. (The third track A agent. Stopped after U7 step (ii) on the coordinator's
change of plan: the remaining proof is to be designed as one set of invariants first.)

- (i) New, `ApiVocab.lean` (public vocabulary, not yet used by any spec): `sentShapeTypes`
  (`sentTypes` ++ `MsgTimeoutNow`, `MsgTransferLeader`), `SentMsgShape st`, `SentMsgShape.ok`
  (with a described type it is `SentMsgOk`), `SentMsgShape.of_msg`. Departures from the frozen text
  (candidate 12, "`SentMsgShape`"): **no `MsgSnap` index bound** (below `2^61`): at `send` the bound
  is not known (`maybeSendSnapshot` reads the storage's snapshot, whose index bound is the storage
  contract's, track B's; J6 of review 10 already called this uncertain for a generic `StorageModel`),
  so `stepIn_intro` keeps its `MsgSnap` premise for now. A forwarded `MsgTransferLeader` may be
  unstamped (`Term = 0`): `send` stamps the follower's term, which may be `0` (the frozen text's "no
  term or the sender's"); a stamped one is the case that needs the `lead` ghost invariant at the
  receiver. Transfer messages carry no entries and no context.
- (ii) `raft.send.spec`'s `SendOk` (`Spec/.../raft__send.lean`): clauses (b) (`MsgApp`,
  `MsgHeartbeat`, `MsgReadIndexResp`, `MsgHeartbeatResp`) and (c') (`MsgSnap`) take `s.term ≠ W64 0`;
  (c) is now exactly `MsgTimeoutNow ∨ MsgTransferLeader` (until then any `mtypeOf = none` type),
  with `ents = [] ∧ ctx = []` and `MsgTimeoutNow → s.term ≠ 0`; (d) (`MsgAppResp`) takes
  `s.term ≠ 0` always (until then only self-addressed). `send`'s proof does not use them yet (that
  is step (iii): `XfOk`'s second clause `∀ m ∈ l, SentMsgShape m.st`, `bt` removed). Internal
  premises added to carry the term (all raft-internal specs, no API change):
  `s.term ≠ W64 0` on `maybeSendAppend`, `maybeSendSnapshot`, `sendHeartbeat`, `sendTimeoutNow`,
  `sendMsgReadIndexResponse`, `sendAppend`, `bcastAppend`, `bcastHeartbeat`,
  `bcastHeartbeatWithCtx`, `handleHeartbeat`, `handleSnapshot`, `handleAppendEntries`; `stepLeader`
  takes `(MsgBeat ∨ MsgTransferLeader → s.term ≠ 0)` (its other sending paths have the term from
  the read-index premise `Hrdnz` or `MsgProp`'s), which `raft.Step`'s `MsgBeat`/`MsgTransferLeader`
  dispatch derives from the ghost (`ownRaftGhost_term_nz`) and hands `wp_Step_MsgBeat`/
  `wp_Step_MsgTransferLeader` as a new premise `s.role = .leader → s.term ≠ 0`; `(s.role = .leader → s.term ≠ 0)` on
  `switchToConfig`, `applyConfChange` and its `specS`; `stepFollower` takes `(MsgApp ∨ MsgHeartbeat
  ∨ MsgSnap → s.term ≠ 0)`. `stepCandidate`'s spec is unchanged (its `m.Term' = s.term ∧ m.Term' ≠ 0`
  covers its handlers and the won election's `bcastAppend`). New lemmas
  `ownRaftGhost_leader_tnz`/`ownStepGhost_leader_tnz` (`InvNodeRun.lean`; from
  `ownRaftGhost_term_nz`) give `RawNode.ApplyConfChange`'s and `node.run`'s `applyConfChange` calls
  the leader premise. `stepLeader/Rest.lean`'s `wp_stepLeader_hbresp`: its `word` calls clear `Htz`
  first (with the term hypothesis in context, a `word` aux proof failed the kernel check:
  "application type mismatch" on `_proof_10`, a Lean/`word` abstraction problem worth a minimal
  repro).

**What the send path taught (for the design).**
- A leader's `term ≠ 0` lives only in the ghost (`ownRaftGhost_term_nz`, via `isCamp_ok`), not in
  `ownRaftPhys`; every leader-side sender needs it threaded as a premise, and so does every
  function that may run at a leader and send (`switchToConfig`'s `maybeSendAppend`/`bcastAppend`,
  hence `applyConfChange` and its `RawNode`/`node.run` callers). A pure `ownRaftPhys` fact `role ∈
  {leader, candidate} → term ≠ 0` would remove most of these premises, at the cost of the role and
  term stores (`becomeLeader`, `reset` inside `becomeFollower` at a leader) taking it; the threading
  was chosen here as the local change, but the design should weigh the phys fact.
- A follower's reply term (`handleAppendEntries`/`handleHeartbeat`/`handleSnapshot`, and
  `raft.Step`'s stale-term `MsgAppResp`) is past `0` from the message: `raft.Step`'s `m.Term' ≠ 0`
  for the stamped types, the term section making `s.term = m.Term'`; the stale case from
  `m.Term' < s.term`.
- The forwarded `MsgTransferLeader` (`stepFollower`, `lead ≠ 0`, `m.Term = 0`) needs no term: it
  may go out unstamped. The stamped one needs, at the receiver, `raft.Step`'s `RestMsgOk` (`m.Term ≠
  0 → m.Term = s.term → follower → lead = 0`), which needs the ghost invariant `lead ≠ 0 →
  isLeader γ lead term` and the forwarder's `isLeader γ m.To m.Term` in `isRaftMsg` (decisions.md,
  "Stage U7", item 2). `NetMsgOk` today rejects a stamped `MsgTransferLeader` (`UnstampedType`).
- `XfOk` (`InvRaftPhys.lean:335`) is where every queued message's facts live (43 mentions there,
  25 `ownRaftPhysCV_intro` sites); `NGhost.bt` is used only for `term ≠ 0` in `send`'s proof
  (`Hxfs.2`) and to gate `SentMsgOk`; step (iii) replaces both by `SendOk`'s new premises.


## U8 v2: the storage contract as range ownership (2026-10-29, branch `raft-unified-storage2`)

The design is candidate 17 rev 3 (`notes/spec-first-study/raft-storage-spec.md`, reviews 1-4).
Steps 1-2 of it are built (vocabulary and contract; raft's log over it); steps 3 (MemoryStorage),
4 (RawNode/node level, the API's `isStorage γ id st`) and the clients are not.

### Architecture (decided at step 1)

- **The class** `StorageModel` (`InvStorage.lean`) is the γ-free range vocabulary only: `storLog`,
  `storEnd`, `storCompacted` and the §1 laws. The old fields (`ownStorage`, `appendTok`,
  `appendedTok`, `storCut`, `storFloor`, `storCap`, `storCert`, `storTermsAt`) are gone.
- **The contract** is parameterized by its two cluster-level pieces, which `InvStorage` (below the
  log, far below the node API) cannot name: `isStorageP (SV : SnapshotM → IProp GF)
  (Bnd : Nat → IProp GF) st` (`InvStorage.lean`). The API module fixes them (step 4):
  `isStorage γ id st := isStorageP (snapshotValid γ) (fun c => ∃ k, ⌜c ≤ k⌝ ∗ (nodeAppliedLb γ id k
  ∨ snapGiven γ id k)) st`, sealed; no client supplies the parameters. `snapshotValid` is defined
  (`InvNodeRule.lean`, exposed, as the design states it).
- **Raft's internal view.** Raft's log is not parameterized: it holds the contract as
  `isStorageV sn st` (`InvStorage.lean`) for internal ghost names `sn : StorNames` (a new
  `LogState.sn`): `∃ SV Bnd, isStorageP SV Bnd st ∗ savedPredOwn sn.gsv □ SV ∗ □(SV persistent) ∗
  □ (∀ c, Bnd c -∗ raftBnd sn c)`, where `raftBnd sn c := ∃ k, ⌜c ≤ k⌝ ∗ (monoNatLbOwn sn.ga k ∨
  monoNatLbOwn sn.gg k)`. So `nodeAppliedLb γ id k` will be `monoNatLbOwn sn.ga k` (here
  `storFloor sn x`) and `snapGiven γ id k` `monoNatLbOwn sn.gg k` (here `storGiven sn k`), for the
  node's `sn` (step 4 ties `sn` to `(γ, id)` and proves the conversion), and the storage's
  snapshot validity travels γ-free as `svCert sn sv` (the `SV` pinned at `sn.gsv`; the node level
  recovers `snapshotValid γ sv` from the pin). This replaces the γ-free certificate registry
  (`storCert`) with a pinned predicate; the raft level (InvRaftPhys's `tsSrc`, StepGhostMode's
  `certLink`) is to carry `svCert` where it carried `storCert`.
- **Review 1's derived contract.** `StorState` is now raft's *view* of its storage (§4's `π` and
  its anchors): `prev` (the compaction point `c` and the dummy's term), `ents` (the physical log
  above it), `pend` (the batch out), `fl` (the applied lower bounds' authority), `fr` (the frozen
  end `f`), `sg` (the snapshots handed out). `ownStorage sn st σ` (a definition now) is what raft
  holds for it: `storCompacted st c`, the frozen prefix `storLog st c □ (e0 :: ents[..fr-c])`
  (the dummy `e0` of `prev`'s term: (T)), the owned part `(fr, kOut)` at `own 1`, the end unless a
  batch is out (P3/N2), and the two authorities. The read triples over the view
  (`isStorageWith (ownStorage sn st) (storCut st) (svCert sn) st`, `isStorage sn st`) are
  **derived** from the contract (`InvStorageRead.isStorage_of_V`), with the statements the log's
  read proofs were written against (only `HSnapshot` and `Hbounded` changed), so `raftLog.term`,
  `slice`, `firstIndex`, `lastIndex` went through unchanged. The old laws (hand-out, absorb,
  floor, the snapshot loan) are lemmas over the ranges (`InvStorageLaws.lean`):
  `ownStorage_handout(_opt)`, `ownStorage_absorb` (the batch back as a frozen prefix `a` and an
  owned rest; raft freezes its own part below `k` when `a ≠ []`), `ownStorage_floor`,
  `ownStorage_lend`/`ownStorage_absorb_snap` (`snapView`), `ownStorage_freeze`.
- **§4's invariant** is today's `ownRaftLog` over the view: P0-P3 are `LogPersistOk`/`PendLogOk` over
  `π = storApp σ σ.pend`, (F) `FrOk` (new conjunct `Hfr`: `fr ≤ max c applying` unless lent, and
  `σ.sg = ls.sg`), (C)/(G) through `FlOk` and the authorities (`sg ≤ c` inside `ownStorage`, so a
  compaction raft did not cause is at most `fl ≤ applying`), (T) inside `ownStorage`. `StoredSnapOk`,
  `Hsksn`, `Hkcert`, `initKsn(Cert)`, `ownRaftLog_terms` are gone. `lentStor` keeps the
  authorities while lent.

### Spec changes during U8 v2 (old → new, why)

- `storLog_valid : storLog st k dq es ⊢ ⌜✓ dq⌝` → only for `es ≠ []`: with `storLog_nil`
  (`⊢ storLog st k dq []`) the design's form is inconsistent (`storLog st k (own 2) []`).
- `isStorage`'s `storCompacted_bound` `={↑N}=∗` → `={⊤}=∗` (in `isStorageP`): raft uses it only at
  `⊤`; the weaker obligation for an implementation. Step 4 may restate the API form with `↑N`
  (it implies the `⊤` form).
- **New law `Hlen`** in the contract: `storLog st k dq es -∗ ⌜es = [] ∨ k + |es| ≤ 2^61⌝ ∗ storLog
  st k dq es` -- the old contract's `Hbounded` (the stable log's last index below `2^61`, which
  `appendEntry`'s no-wrap needs and no invariant of the log can carry), restated over ranges. The
  design has no bound at all; without one `raft.appendEntry` is unprovable (`InvRaftlog.lean`'s
  header). Client-visible once `isStorage γ id st` is defined: **approved by the user** (via the coordinator, 2026-10-29), as are the two deviations above.
- `HEntries`' post: the design's "cut by max" is the old prefix statement
  (`es <+: ((a ++ b).drop (lo - k)).take (hi - lo)`), as before.
- `raftLog.snapshot.spec`: the storage's snapshot is at or past the log's boundary and valid
  (`svCert ls.sn sv`); the pending one as before (in `ksn`, at or below `committed`, the log's
  base). Gone: the storage's snapshot's commit bound and term (`StoredSnapOk`), the
  "or at most the floor" disjunct and the `storCert` certificate.
- `raftLog.restore.spec`: no `storCert` premise (the restored snapshot's certificate is no longer
  registered in the storage).
- `newLogWithSize.spec`: takes `isStorage sn st ∗ ownStorage sn st σ` with `σ.fr = prev.index`,
  `σ.sg = 0`; no `StoredSnapOk` premise, no `initKsnCert`; `ksn := []`, `sn := sn`.
- `ownRaftLog_absorb` takes `appendReceipt ls.storage ls.unpersisted a` (the batch back, `a` its
  frozen prefix) and `⌜a ≠ [] → k - 1 + |a| ≤ applying⌝`; `ownRaftLog_raise_floor` gives
  `storFloor ls.sn x`; `ownRaftLog_lend` gives the ranges above the frozen prefix with the end and
  `storGiven ls.sn s` (`lendLog`: `sg := max sg s`); `ownRaftLog_absorb_snap` takes the
  compaction point at the snapshot, the dummy, `ls.stored` after it and the end, with
  `⌜ls.sg ≤ s⌝`.

Step 3a (the raft level, 2026-10-29):

- **The snapshot's commit bound (2026-10-29, decided by the coordinator: option (A))**. `maybeSendSnapshot`'s
  `SnapOk` needs the storage's snapshot at or below the *leader's own* commit index and an entry id of
  its log; the snapshot's validity (`snapshotValid`, a committed prefix of the cluster) does not give
  the first (a new leader's commit index may lag the cluster's: its client may have frozen and
  snapshotted entries the cluster committed before it learned so). New: a third cluster-level
  parameter of the contract, `isStorageP SV Bnd DL st`, and `HSnapshot`'s post
  `(⌜Index = 0⌝ ∨ SV sv ∗ DL (uint.nat Index))` (old: `SV sv` alone). The API (step 4) fixes `DL i :=
  (∃ l, deliveredLogLb … l ∗ ⌜i ≤ |l|⌝) ∨ snapGiven … i'` (the node's delivered committed prefix
  reaches `i`, or a snapshot raft handed out does); the client's `CreateSnapshot(i)` then needs the
  delivered prefix of length `≥ i` (step 3, MemoryStorage: only noted here). Raft reads it, with the
  snapshot's validity, as `raftDL sn i t := i ↪[sn.gd]□ t ∨ ∃ k, ⌜i < k⌝ ∗ monoNatLbOwn sn.gg k`
  (`isStorageV`'s new conversion `□ ∀ sv, SV sv -∗ DL (Index) ={⊤}=∗ raftDL sn Index Term`, at `⊤`
  so that step 4 may open an invariant): a term raft certified at a committed index, or an index
  below a snapshot handed out (so below the compaction point raft holds). Internal ghost state:
  `StorNames.gd` (a ghost map `Nat → w64`, authority `σ.dt` in `storAuths`) and the invariant
  `DtOk σ.dt ls` (in `FrOk`): every key at most `committed`, of the log's term there once at or past
  the boundary. Step 4 issues the keys (from the authority, at the delivered indices; `DtOk` gives
  what it may issue). Raft's derived `HSnapshot` gives `σ.dt.lookup Index = some Term`;
  `raftLog.snapshot`'s storage branch now also gives `Index ≤ committed` and `plogTermAt … Index =
  some Term` (as its pending branch did).
- `newLogWithSize.spec`: also `σ.dt = ∅`.
- `raftLog.restore.spec`: takes `ksnCert ls.sn (snapTrip sv lists)` (U8 v2 step 2e had dropped the
  certificate premise; the received snapshot's certificate is kept in the log again, now as a pin:
  below). `raftLog.snapshot.spec`'s pending branch gives `ksnCert ls.sn (snapTrip sv lists)`.
- **The snapshots' certificates at raft's level** (old: the storage's registry `storCert st k`, both
  ways to `raftSnapCertD γ k`, `storCertOk γ st`): two γ-free pins of raft's storage names,
  `svCert sn sv` (a stored snapshot's validity, the contract's `SV`, pinned at `sn.gsv`) and the new
  `ksnCert sn k` (a received snapshot's certificate, pinned at the new `StorNames.gk`; `ownRaftLog`'s
  `#Hkcert ∷ ksnCerts ls.sn ls.ksn`, every snapshot the node may send). `storCertOk γ sn` (now over the
  names): `svCert sn sv ={E}=∗ raftSnapCertD γ (snapTrip sv lists)`, `ksnCert sn k ={E}=∗
  raftSnapCertD γ k` and back (`raft.Step`'s `MsgSnap` arm pins the message's). `certLink γ sn :=
  storCertOk γ sn` (old: `⌜γ.reNoSnap⌝ ∨ storCertOk γ st`); `ghostRest` keys it by `s.gh.sn`.
- **`NGhost.sn`** (new field, a mirror of `LogState.sn`; `GhLogOk`'s third conjunct `ls.sn = g.sn`):
  every step keeps the ghost record (`NetFrame`, `LocalFrame`, `SnapStep`), so the certificates the
  struct and the ghost state hold are keyed by it without new frame conjuncts. `SnpKeep` also keeps
  `sn`. `LogGhOk.of_snap`/`of_off` take `ls'.sn = s.gh.sn`; `of_fields` has `hsm := by rfl`.
  `ghost_stepCD(S)`'s and `ownStepGhost_congr`/`ghostRest_keep`'s storage hypotheses are now unused
  (the latter two's `hst` is `s'.gh.sn = s.gh.sn := by rfl`).
- `tsSrc st ty snap` → `tsSrc sn ty snap := ⌜ty ≠ MsgSnap⌝ ∨ ∃ sv, ⌜snap = some sv⌝ ∗ (svCert sn sv ∨
  ksnCert sn (snapTrip sv lists))`; `qSrc(s)` over the names; `ownRaftPhys`'s `Hscert` is `qSrcs s.gh.sn
  …` (old: of `s.logst.storage`). New `rcvSrc sn ty snap` (only `ksnCert`): `stepFollower`'s and
  `stepCandidate`'s premise (old: `tsSrc`), which `handleSnapshot`/`raft.restore` (`ksnCert s.gh.sn`,
  old `storCert s.logst.storage`) consume.
- **The no-snapshot mode dropped at raft's level** (decision approved by the user via the coordinator):
  `NsCap ns st := ⌜ns = false⌝` (old: `□ (⌜ns⌝ -∗ storCap st 1)`; name kept for its call sites),
  so every node has `NGhost.ns = false` and, by `NsLink`, its cluster `reNoSnap = false`; the mode's
  facts (`LogNsOk`, `PrOkN`'s `PrLo`, the `ns = true` branches) hold vacuously. `ownRaftPhysC_set_ns`
  (the mode set with the storage's cap) is removed; new `ownRaftPhysC_sn` reads `ns = false` and the
  names' mirror. `raft.maybeSendSnapshot.spec` no longer takes `s.gh.ns = false` (reachable in every
  cluster). The other `s.gh.ns = false` premises (`raft.restore`, `handleSnapshot`, `stepFollower`,
  `raft.Step`'s `MsgSnap → ns = false`, `ReplSends`' last conjunct) are kept: derivable from
  `ownRaftPhys` now; step 4 removes them with the mode. **What etcd's server loses**: its transport
  excludes `MsgSnap` (the boot contract's no-snapshot mode); with the mode gone at raft's level a
  server node is a node of a cluster with `reNoSnap = false`, which may send and receive snapshots,
  so the server's proof must handle `MsgSnap` or get the exclusion back. **The fallback to put to the
  user in the client-repair phase**: a client-chosen cap witness `storCompactCap st k` with
  `storCompacted st c ∗ storCompactCap st k ⊢ ⌜c ≤ k⌝` (a storage that promises never to compact past
  `k`), which would restore the mode for such clients (not built).
- `newRaft.spec`: takes `sn`, `isStorage sn st ∗ ownStorage sn st σ` with `σ.fr = prev.index`,
  `σ.sg = 0`, `σ.dt = ∅` (old: `(σ.ss.index = 0 ∨ σ.ss = σ.prev)` and `initKsnCert`); the
  `InitialState` triple over `ownStorage sn st σ` at the same `σ` (old: any `ss'`); post
  `s.logst.sn = sn` and `s.gh = { sn := sn }` (old `s.gh = {}`).
- Moved, so that raft's level builds without the node level: `propMsgM`, `ccEntryM`
  (`InvRawnode` → `ApiVocab`), `ownRaftLog_last_bound`, `ownRaftPhysC_last_bound` (`InvRawnode` →
  `InvRaftPhys`), the generic slice lemmas of `LemmasMemstorage` (→ new `LemmasEnts`).
  Removed until step 4 restates them: `ApiVocab`'s `readyOut`, `snapReceipt`, `advReceipt` (over the
  old `StorState`/`appendRight`/`storCert`).

Step 3 (MemoryStorage, 2026-10-29; the approved shapes, generic until step 4):

- **Generic form**: the storage's invariant is `memStorInvP ms γs J` (`InvMemstorage.lean`) at
  justification parameters `J : MemJust GF` (`J.SV` snapshot validity, `J.B k` compaction
  justification, `J.DL i` delivered bound; persistent, `J.B` timeless), and the law is
  `memStorage_isStorageP : memStorInvP ms γs J -∗ memStorReg ms γs -∗ isStorageP J.SV (memBnd J) J.DL
  (memStorIface ms)` (`MemstorageInstance.lean`; `memBnd J c := ∃ k, ⌜c ≤ k⌝ ∗ J.B k`). Step 4
  instantiates `J` (`SV := snapshotValid γ`, `B k := nodeAppliedLb γ id k ∨ snapGiven γ id k`, `DL` the
  API's) to get the approved `memStorInv ms γs γ id` and `… ⊢ isStorage γ id st`. **Step 4 must make
  `nodeAppliedLb`/`snapGiven` timeless** (`storCompacted_bound` reads `J.B` out of an invariant under an
  update with no program step); `SV`/`DL` need not be (read in `Snapshot()`, a step strips the later).
- The method specs are over the storage's names (`memLog γs`, `memEnd γs`, `memCompacted γs`,
  `memSnapExact γs`; the instance's `storLog`/`storEnd`/`storCompacted` for `memStorIface ms` are these
  under `memStorReg ms γs`: `memStorLog_to`/`_of`, `memStorEnd_to`/`_of`, `memStorCompacted_to`/`_of`).
- `NewMemoryStorage`: `memLog γs 0 □ [e₀]` (old/approved: `own 1`, the client to freeze it): the lock
  keeps the dummy at the compaction point frozen (otherwise `Append` over an owned key `0` could change
  the term `Term(0)` reads); a frozen range is what the client would make anyway. Also gives
  `memStorLock ms γs` (the mutex, persistent) and **`memStorFresh ms γs`, the allocation's fuel**
  (the authority of the justified compaction points and the snapshot's home, which the lock does not
  hold; `memStorInvP_alloc` consumes it, with `J.B 0`), as the old design's `memCertAuth` was.
  `memStorReg ms γs` is not in the post: registering needs the registry's authority and the pointer's
  absence, the client's (`memStorReg_register`), as before.
- `Append`: `es = []` gives the pre back unchanged (a no-op); the batch's indices consecutive
  (`es[j].Index = k + j`) and `k + |es| ≤ 2^61` as premises; `entsPts s dq es` (the old argument form).
- `ApplySnapshot`: also `⌜s < 2^61⌝` (the dummy's range must satisfy `Hlen`); the justification is
  three premises `J.B s ∗ J.SV sv ∗ J.DL s` (step 4: `snapGiven γ id s` gives `B` and `DL`); also gives
  `ownSnapM sp dq sv` back. **Step 4 must supply `s < 2^61`** for a snapshot `Ready`.
- `CreateSnapshot`: `J.SV (memSnapCreated sv0 i e.Term oc bs) ∗ J.DL i` (the stored conf state `sv0`'s
  when `cs = nil`); `ErrSnapOutOfDate` also gives `snap = null` and `data ↦* bs` back.
- `Compact`: also `memStorInvP` (it registers `x`'s justification).
- `Snapshot`: one spec (the contract's); the application's second spec is gone.
- **`InitialState` (finding for step 4)**: it reads (and may write the `AutoLeave` of) the stored
  snapshot without the lock, which the locked `Snapshot()` writes (`ms.snapshot =
  EnsureSnapshot(ms.snapshot)`): a real race (`issues/raft-memorystorage-initialstate-unlocked.md`). The
  contract's `Snapshot()` needs no exclusive resource, so `InitialState` can only be specified before the
  storage is a `Storage`: its pre is `memStorMeta ∗ memStorFresh` (the snapshot is in the fuel until
  `memStorInvP_alloc`). `newRaft.spec` takes `isStorage` and the `InitialState` triple together, which a
  `MemoryStorage` cannot meet: step 4 must restructure it (e.g. `InitialState`'s triple's post gives
  `isStorage`, the client allocating the invariant after `InitialState` returns).
- Internal: `MemOk` records that the stored entries are numbered by position (`Compact`'s new dummy
  takes its index from the stored entry).
- `memSnapLb` (the stored snapshot's lower bound, for etcd's two writers) is **not built**: the server's
  repair.

Step 4 (the node level, 2026-10-29; in progress):

- **U9 ahead of schedule** (the coordinator's decision): the static cluster's variants that touch
  the storage (`StartNode.spec`, `RestartNode.spec`, `node.Advance.spec`, with their `Linked`
  results) are dropped, not restated; the unified cluster (`isCluster`, `RestartNode.unifiedSpec`)
  is the one that matters; the dynamic variants are kept only where they come for free.
- `isStorage sn st` (raft's derived view, `InvStorage.lean`) renamed `isStorageD sn st`, to free
  the name for the API's `isStorage γ id st`.
- **The API's pieces** (`InvNodeRule.lean`, sealed over `InvApi.lean`'s `ApiImpl`):
  `nodeAppliedLb γ id k := ⌜k = 0⌝ ∨ ∃ sn, nodeStorNames γ id sn ∗ (monoNatLbOwn sn.ga k ∨
  monoNatLbOwn sn.gg k)` (an applied lower bound: the floor raft published, or a snapshot it
  handed out, which `Advance` applies), `snapGiven γ id k := ∃ sn, nodeStorNames γ id sn ∗
  monoNatLbOwn sn.gg k`, both persistent and timeless; `nodeStorNames γ id sn`: the node's table
  entry (`Cluster.nodeTab`, `nodeTabOk`) names its storage names (`CfgNames` extended by the five
  names of `StorNames`, `NodeNames.sn`). `isStorage γ id st := isStorageP (snapshotValid γ)
  (storBnd γ id) (storDL γ id) st`, with `storBnd γ id c := ∃ k, ⌜c ≤ k⌝ ∗ (nodeAppliedLb γ id k
  ∨ snapGiven γ id k)` and the delivered bound in existing client names only, `storDL γ id i :=
  ∃ n N l, isNode n γ N id ∗ deliveredLogLb n γ N l ∗ ⌜i ≤ |l|⌝` (kvreconf snapshots between
  applying a `Ready`'s entries and `Advance`, so an applied bound would not do). Internally the
  driver's `dlvLb γn ds` carries raft's certified terms of `ds` (`dlvKeys sn ds`, the keys
  `j + 1 ↪[sn.gd]□ ds[j].Term'`), which a `Ready` issues for its committed entries
  (`ownRaftLog_certify`, `LogState.dtk` the certified height, `SdtTie` now `dtk = |delivered|`):
  the conversion `isStorage γ id st ⊢ isStorageV sn st` needs no invariant.
- `snapshotValid γ sv` (2026-10-29, approved): also `uint.nat Index < 2^61` and the `ConfState`'s
  four lists of total length at most `2^62` (raft's certificate, `SnapListsOk`, needs both, and
  nothing in the definitions gives them: a joint configuration may list `2^62 + 2` ids; the
  client proves them where it makes the snapshot, as the old `snapshotCert_make`'s `SnapListsOk`).
  `SnapValidCert.lean`: the protocol-level lemma from the pieces to `raftSnapCertD`.
- **The boot storage (decision (a) refined, approved as (B))**: `newRaft` reads `FirstIndex` and
  `LastIndex` (`newLogWithSize`) *before* `InitialState`, so raft cannot be given `isStorage`
  only after `InitialState`. `RestartNode.unifiedSpec` takes one premise, a boot bundle with a
  client frame `R`: persistent triples of `FirstIndex` (`1`), `LastIndex` (`0`) and
  `InitialState`, whose post includes the update to `isStorage γ id st ∗ storLog st 0 □ [e₀] ∗
  storEnd st 1` (`e₀.Term' = 0`); `MemoryStorage`'s instance of it is a law (`memStorFresh`,
  the lock: `FirstIndex`/`LastIndex` need only the lock, the snapshot being in the fuel).
- `FrOk`'s first conjunct: the frozen end at most `committed` and below `inprogress` (and below a
  pending snapshot not yet handed out), not `max c applying`: a `Ready` freezes its committed
  entries below its batch at the hand-out, before `acceptReady` moves `applying`
  (`ownRaftLog_handout`'s new frozen range, `frozenRdy`); `ownRaftLog_lend` also gives the lend's
  start at most the snapshot's index (`ApplySnapshot` needs `j ≤ s`).
- The `Ready`'s storage hand-out and its receipt over the ranges (`ApiVocab.lean`): `readyOut st
  sn es L` (no snapshot: `appendRight st es`; a snapshot: the ranges from `k ≤ s` with the end, and
  `storGiven sn s`), `ceFrozen st n ce es` (the committed entries below the batch, frozen),
  `snapReceipt st l es` (§3's `Advance` pre after a snapshot: the half snapshot, `storCompacted st
  s`, the dummy of its term frozen, `es` owned after it, the end), `advReceipt st n es L` (no
  snapshot: `∃ a, appendReceipt st es a` with the frozen prefix within the `n` delivered).
- `RNState.sn` (raft's storage names, constant; `ownRawNode`'s `Hstor` now also `rs.sn =
  s.logst.sn`); `ownRawNode_raise_floor` gives `storFloor rs.sn x` (no `storTermsAt`, no `D`);
  `ownRawNode_appended` takes the frozen prefix `a` within `delivered`; `ownRaftPhys_set_ns` only
  at `b = false` (no `NsCap`).

- **kvreconf-snapshot-thread (2026-10-30, user-approved new client-visible ghost state)**: the
  exclusive `memSnapExact γs sv` replaced by the persistent `memSnapLb γs i` (the stored snapshot's
  index `≥ i`, monotone; `MemStorNames.sl`, the authority in the lock) — the deferred two-writer
  form, now built. `CreateSnapshot(i)`: both outcomes give `memSnapLb γs i` (no exact knowledge,
  `ErrSnapOutOfDate` tolerated); `Compact(x)` takes `memSnapLb γs x` (no `sv0`, no `x ≤ sv0.Index`
  premise); `ApplySnapshot` takes no snapshot token (its success proved in the lock's invariant, as
  before) and gives `memSnapLb γs s`. **Deviations (logged for the user):** (1) the writers
  (`CreateSnapshot`, `ApplySnapshot`) take `memSnapLb γs 0`, and `NewMemoryStorage` gives the
  exclusive `memSnapNone γs` (`MemStorNames.pr`) instead, opened by `memSnapNone_open :
  memSnapNone γs ==∗ memSnapLb γs 0`: R1 of the server's repair design (`Snapshot()` on a storage
  that never stored a snapshot answers exactly the empty one) needs a fact the writers cannot
  invalidate, so they need a permission (persistent, so two writers share it); `Snapshot`'s one
  spec takes `(if b then memSnapNone γs else emp)` and, for `b = true`, says `sv = memSnapEmpty`
  (the contract law uses `b = false`). (2) `CreateSnapshot`'s `cs` must be non-`nil` (`ownCSM cs dq
  c`, was `memCsArg`): a `nil` one keeps the stored snapshot's conf state, which a writer beside
  another does not know; kvreconf and etcd pass one. **Note for the server's repair:** the old
  `SnapTake.lean` says `ep.confState` may be `nil`; the server must pass a non-`nil` one or show it
  non-`nil`. `memSnapMade i t c bs` names the stored snapshot (`memSnapCreated_some`).

### Where step 4 stopped (2026-10-29, the user's wrap-up)

The tree builds up to the log and raft level and `InvRawnode`; the node level does not build.
Committed and building: the log level's step-4 lemmas (`ownRaftLog_handout`'s frozen range,
`ownRaftLog_lend`'s `k ≤ s`, `ownRaftLog_certify`, `FrOk`'s new first conjunct, `LogState.dtk`,
`dtk` in `logStoreRec`/`SnapLogStep`), every `raft.*`/`raftLog.*` proof and `newRaft`, `ApiVocab`'s
new storage vocabulary, `InvRawnode`, `SnapValidCert`, `LemmasCeFrozen`. The unbuilt node-level work
is `notes/u8v2/step4-node-wip.patch` (apply with `git apply`): `InvRawnodeReady` (`rdyLog`'s
certified height `dk`, `dlvAfter` moved there, `ownRaftLog_rdy_out` and `ownRawNodeReady_handout`
rewritten with the frozen `ceFrozen` and the keys `dlvKeysAt`, `ownRaftLog_certify_list`,
`ownRaftLog_applying_lt`; still ~15 errors, mostly `acceptReady`'s consumers of `rdyLog`/`Hgh0`
projections and the snapshot `Advance` side), `InvNodeChan` (`NodeNames.sn`, `readyData`'s
`readyOut`/`ceFrozen`, `readyP`'s `dlvKeys`, `dlvLb` with the keys, `runCfg`'s keys and `rs.sn =
γ.sn`, `reqWit` over `storFloor γ.sn`, `advDep`'s `sn`), `InvNodeRun` (`runCfg_extend` with the
keys), `InvAdvance` (the none branch over `advReceipt`'s frozen prefix), `InvApi` (`CfgNames` with
the storage names, `nodeStorNames`, `nodeAppliedLbU`, `snapGivenU`, the certificate registry and
`storageCertLink` removed, `nodeDriver` keeps `storGiven` after a snapshot `Ready`), `InvNode`
(sealed `nodeAppliedLb`/`snapGiven` with their laws, `readySnap`'s new storage part,
`storageCertInv`/`storageCertLink` removed), `InvNodeRule` (`snapshotValid`'s two bounds,
`storBnd`, `storDL`, `isStorage γ id st`, `bootStorage`), and the specs `RestartNode.spec` (the
unified one, over `bootStorage`; the static one dropped) and `node.Advance.spec` (the unified one,
post `nodeAppliedLb γ id |st.delivered|`; static and dynamic dropped).

Remaining, in order: `InvRawnodeReady` (finish: `acceptReady` with `rdyLog`'s `dk`, the
`SdtTie` of the accepted state from `dk`); `RawNode__Advance` (the snapshot receipt over
`snapReceipt`, `ownRaftLog_absorb_snap`'s new `Hsid` from `LoanOk` and `SnpOk`: the loan's snapshot
is pending with `sip = true`, or a later one is); `InvNodeChan`/`InvNodeRun`/`node__run` (the
Ready arm: keys and frozen range through `readyP`; the advance arm); `InvApi`/`InvApiDyn`/`InvNode`
(`wp_readyRecv_impl` builds `dlvLb` with the keys and `readySnap` from `readySnapData`, converting
`storGiven γn.sn` to `snapGiven γ id` by `nodeTabOk_storNames`); the conversion `isStorage γ id st
⊢ isStorageV sn st` and the pins (`sn.gsv` at `snapshotValid γ`, `sn.gk` at `raftSnapCertD γ.raft`)
with `storCertOk γ.raft sn` from `SnapValidCert` (a module above `InvNodeRule`); `RestartNode` over
`bootStorage` (allocate `sn`'s authorities and the table entry, `newRaft` over the boot bundle);
`MemstorageInstance` (`memStorInv` at the API's `J`, its `isStorage` law, `memStorage_bootStorage`);
the other node-level proofs (mechanical: `Hstor`'s pair, `runCfg`'s patterns, `Hgh0` projections);
StartNode/static variants deleted with their `Linked` results; `Link.lean` regenerated.

The boot bundle at `newLogWithSize` (decision (B)) is built but not committed, since `newRaft`
does not yet use it: `notes/u8v2/step4-boot-newLogWithSize.patch` (the spec over a frame `R` with
`FirstIndex`/`LastIndex` answering `1`/`0`, the post a wand from `isStorageD sn st ∗ ownStorage
sn st σ0` to the log). Its helper's findings: `wp_apply` on a hypothesis triple with no binders in
its post drops the continuation (workaround `wp_apply_raw H $$ [$HR]; inext; iintro HR`), and
`word` on fully concrete goals failed the kernel's check (replaced by `rfl`/`simp`): candidates for
`notes/perennial-changes.md`. Its open question: should the caller's frame come out of the update
(`R' ={⊤}=∗ isStorageD ∗ ownStorage σ0 ∗ Q`)?

### What builds, what is broken (at the step-2 commit)

Builds: `InvStorage`, `InvStorageRead`, `InvStorageLaws`, `InvRaftlog`, `InvReadylog`,
`LemmasRaftlogW`, `InvNodeRule`'s `snapshotValid`, and every `raftLog.*`, `unstable.*` and
`newLogWithSize` spec and proof (no `sorry`, no new axiom; `#print axioms` of `isStorage_of_V`,
`raftLog.{term,slice,snapshot,stableTo}.wp_proof`, `newLogWithSize.wp_proof`, `ownRaftLog_{absorb,
lend,absorb_snap}`: Perennial's standard ones only).

Broken (expected): everything that uses the removed names, i.e.
- the raft level: `StepGhostMode` (`storCertOk`, `certLink` in `ghostRest`), hence `InvRaftPhys`
  (`tsSrc`/`qSrc` carry `storCert`; `NsCap` uses `storCap`) and everything above it: `raft.*`
  (`appendEntry`'s `Hsksn`, `loadState`, `maybeSendSnapshot`/`raft.Step`'s `MsgSnap` arms,
  `stepFollower`/`stepCandidate`), `newRaft`;
- the RawNode/node level (step 4): `InvRawnode*`, `RawNode__*`, `ApiVocab`, `InvApi*`, `InvNode*`,
  `StartNode`, `RestartNode`, `setupNode`, `node__Advance`, ...;
- `MemoryStorage` (step 3): `MemstorageInstance`, `InvMemstorage`, `MemCertLink`, `MemoryStorage__*`;
- the clients (kv, server, examples).

### What builds, what is broken (at the step-3a commit, raft's level)

Builds: everything up to raft's level -- the log level as at step 2, and `StepGhostMode`,
`InvRaftPhys`, `ApiVocab`, every `raft.*` spec and proof, `raft.Step` with every arm, `stepLeader`,
`stepFollower`, `stepCandidate`, `newRaft` (no `sorry`, no new axiom; `#print axioms` of
`raft.Step`, `newRaft`, `raft.{maybeSendSnapshot,restore,appliedTo}`, `raftLog.{snapshot,restore,
append}` and `isStorage_of_V`: no `sorryAx`, no axiom of this repository's beyond the existing ones).
Broken (expected): the RawNode/node level (step 4), `MemoryStorage` (step 3), the clients, and the
raft-level proofs that import node-level modules (`IsEmptySnap`, `IsEmptyHardState`: through
`InvRawnodeReady`/`InvBoot`/`NewRawNode`; `ConfRule`, `ConfPolicy`, `DecFold`, `ConfchangeApi*`:
through `InvNode`/`InvApi`), until step 4.

### What builds (at the step-3 commit, MemoryStorage)

Builds (targeted `lake build`, no `sorry`, no new axiom; `#print axioms` of `memStorage_isStorageP`,
`memStorInvP_alloc`, `memCompacted_bound` and every `MemoryStorage.*`/`NewMemoryStorage` `wp_proof`:
Lean's and Perennial's Go-model axioms only): `InvMemstorage`, `MemstorageInstance` (instance + law),
every `MemoryStorage__*` spec and proof, `NewMemoryStorage`, `LemmasMemstorage` (a re-export of
`LemmasEnts`). Removed: `MemstorageAU`, `MemCertLink`. `Link.lean` not regenerated (the node level is
broken); the MemoryStorage proofs keep their callee hypotheses (`MemstorageInstance` takes the five read
specs as hypotheses).

### What remains (next steps, in order)

1. **Step 4** (the node level): the API's `DL` (`deliveredLogLb`-based, or `snapGiven`), and its
   conversion to `raftDL` (issue `i ↪[sn.gd]□ t` from `σ.dt`'s authority at the delivered indices:
   `DtOk` says which; a lemma `ownRaftLog_certify` is to be written in `InvRaftlog`; the authority
   cannot hand out an existing key's fragment again, so either `storAuths` keeps `[∗ map] k ↦ v ∈
   σ.dt, k ↪□ v` beside it or the issuer keeps what it issued); pin `sn.gk` at
   `raftSnapCertD γ` and prove `storCertOk γ sn` (`certLink`) from the pins (`svCert` →
   `raftSnapCertD` needs `snapshotValid γ sv ⊢ raftSnapCertD γ (snapTrip …)`); `nodeAppliedLb`/
   `snapGiven` (sealed) over `storFloor`/`storGiven` of the node's `sn`; `isStorage γ id st` and
   `isStorage γ id st ⊢ isStorageV sn st` (allocate `gsv`, `gd`, `gk`; the `Bnd` and `DL`
   conversions); the `Ready`/`Advance` hand-outs (`readyOut`/`snapReceipt`/`advReceipt`, removed
   from `ApiVocab`, over the ranges: `appendRight`, `appendReceipt`, the frozen `ceBelow` via
   `ownStorage_freeze`/`ownStorage_frozen`); (G) `sg ≤ s` at `absorb_snap`; the no-snapshot mode's
   node-level plumbing (`reNoSnap`, `NGhost.ns`, `RNMode`, `NsLink`'s `ns`, the remaining
   `s.gh.ns = false` premises) removed; `newRaft`'s new premises (`σ.dt = ∅`, `s.gh = { sn := sn }`).
2. **Step 3: done** (above). What step 4 takes from it: instantiate `MemJust` (timeless `B`), supply
   `s < 2^61` at `ApplySnapshot`, restructure `newRaft`'s `InitialState` premise (above).
3. **Clients**: etcd's server loses the no-snapshot mode (above); the fallback `storCompactCap` is
   to be put to the user.
## Track A hand-off (2026-10-29)

**Done on `raft-unified`.** Each commit builds `Link`, `Linked`, `Results`, `Api`; there is no `sorry`, and the only
raft-specific axiom is `ccDecodeV2_nil`.
- U5's committed conf-entry laws (`f4b2a4d84e`).
- U7, in part: `Tick` and a stepped `MsgTimeoutNow` take raft's own time receipts (`32ba2bdcd8`). The
  node API's `stepIn` is `⌜ml ≠ null⌝ ∗ ∀ γn, ⌜NodeOk⌝ -∗ ⧗ 1 -∗ stepP` (`InvApi.lean`); `node.Step`
  takes the receipt at its `nil` comparison.
- U9a, stopped nodes, `nodeRunning` (`63ad16cafa`; "U9a as built" above).
- S1, proposals over duplicating networks (`6657289b28`; "S1 as built" above). If the S1 helper sends
  a final report, it adds nothing beyond that entry.

**Open, in order.** The design is in `notes/decisions.md`, "Stage U7: messages, track A".
1. **`node.Campaign.spec`.** (Done, `b97c601195`; "Spec changes during track A (fresh)".) kvreconf calls it (`reconf.go:106`). The coordinator chose option 1, an
   internal case in `netP` with no public change.
   - `MsgHup` is not in `netStepTypes` (`ApiVocab.lean:267`). Add an *internal* local case for it in
     `netP` (`InvNodeChan.lean`, near `netP_local`); do not change the public `NetMsgOk`.
   - A hup raises the term one past `netP`'s `termLB` ceiling. So `run`'s `recvc` arm
     (`node__run.lean`, around `budget_step`) needs a budget step with a time receipt, as a tick's
     (`budget_spend`). Take the receipt from a Go step of `Campaign`'s own, as `node__Tick.lean` does
     at a `StructFieldRef`.
   - Model the spec on `node__ForgetLeader.lean`: an API spec over `isNode`, a raw `specRaw`.
2. **`node.Status.spec`** (Done, `8ed7fe817a`; "Spec changes during track A (fresh)".) (`cluster.go:407`). A reduced spec does not work, since `Status`'s send on
   `status` must supply its payload up front.
   - It needs `run`'s status arm, with internal specs of `getStatus`, `getBasicStatus`,
     `getProgressCopy` (through `Visit`) and `Config.Clone`.
   - Post: an owned `Status` value. On a stopped node, the `done` arm returns `Status{}`.
3. **U7's rest**, now without a transfer mode (the user's decision above):
   - *Status (third track A agent, 2026-10-29): steps (i) and (ii) done ("Spec changes during track
     A (third)", with what the send path taught); stopped there on the coordinator's change of plan
     (the remaining invariants to be designed as one reviewed design). Next: (iii).*
   - `SentMsgShape` in every cluster. `SendOk`'s stamped clauses take `s.term ≠ W64 0` from each
     caller: a leader has it from `ownRaftGhost_term_nz`; a follower after the term section has `m.Term
     = s.term ≠ 0`. `XfOk`'s second clause becomes `∀ m ∈ l, SentMsgShape m.st`, and `NGhost.bt`
     goes (`InvRaftPhys.lean:335`).
   - `stepIn_intro` admitting every sent message, a re-forwarded `MsgTransferLeader` included. This
     needs three pieces:
     - the ghost invariant `lead ≠ 0 → isLeader γ s.lead s.term`, as its own conjunct of
       `ownRaftGhost` (`Protocol/GhostState.lean:2002`; touch only the rules that move `lead` or
       `term`);
     - the forwarded request carrying `isLeader γ m.To m.Term` in `isRaftMsg`;
     - at the receiver, `isLeader_unique` and `LeadOk`, which discharge `raft.Step`'s `RestMsgOk`
       premise.
   - `node.TransferLeadership.spec` over `isNode` only (drop `leaderTransferOn`); `NGhost.xf` is false
     in the decision cluster.
   - The read-credit exchange, so that `ReadIndex` and a forwarded `MsgReadIndex` need no client
     `readCredit`. Add an invariant `∃ k, ⧗ k ∗ rdCred γ.raft (2^64 - 2 - k)` in the decision cluster;
     `stepIn`'s wand then becomes a `⊤` update, and `cluster_alloc_dec` loses `readCredits`. Then
     add `msgCredits_intro : st.msg.Type' ≠ MsgProp → ⊢ |==> msgCredits` (S1's text).
   - *Scoping by the second track A agent (2026-10-29, not started).* `raft.send.spec`'s `SendOk`
     (`Spec/go_etcd_io/raft/v3/raft__send.lean:106`): clause (b) (`MsgApp`/`MsgHeartbeat`/
     `MsgReadIndexResp`/`MsgHeartbeatResp`, stamped), (c) `MsgSnap` (stamped), (c') the undescribed
     types (`MsgTimeoutNow`, a forwarded `MsgTransferLeader`; today `s.gh.xf = false`), (d) `MsgAppResp`
     (`s.term ≠ 0` only when `To = id`). `raft.send`'s callers (16 proof files): `maybeSendAppend`,
     `maybeSendSnapshot`, `sendHeartbeat`, `sendTimeoutNow`, `sendMsgReadIndexResponse`, `appendEntry`,
     `campaign`, `handleAppendEntries`, `handleHeartbeat`, `handleSnapshot`, `stepFollower`,
     `stepLeader` (+ `stepLeader/Rest`), `raft.Step` (+ `raft__Step/Base`). A leader's `term ≠ 0` is
     derived in `raft.Step` from the ghost (`ownRaftGhost_term_nz`, `raft__Step.lean:699`, `:898`) and
     passed down as a premise (`stepLeader.spec:348`, `appendEntry.spec:175`,
     `releasePendingReadIndexMessages`); the leader-side send helpers (`maybeSendAppend`,
     `maybeSendSnapshot`, `sendHeartbeat`, `sendTimeoutNow`, `sendMsgReadIndexResponse`, and
     `bcastAppend`/`bcastHeartbeat*` above them) would take the same premise. `XfOk`'s users:
     `InvRaftPhys.lean` (42 mentions), `raft__send.lean`'s `XfOk` step lemma (line 67),
     `InvRawnodeReady`, `LemmasReadyR`, `StepGhostMode` (`GMode`'s `xf`/`bt`), `RawNode__Bootstrap`,
     `newRaft`. Suggested order: (i) `SentMsgShape` (ApiVocab, beside `SentMsgOk`); (ii) `SendOk`'s
     stamped clauses take `s.term ≠ 0`, the callers' specs the leader premise; (iii) `XfOk`'s second
     clause unconditional, `bt` removed; (iv) `isRaftMsg`/`NetMsgOk.of_sent` from `SentMsgShape`.
     Commit after each, building `Link`.
4. **U9**: one spec per function; the old families deleted. (Coordinator, 2026-10-29: track B drops
   the static `StartNode.spec`, `RestartNode.spec`, `node.Advance.spec` and their Linked results; merge
   `raft-unified-storage2` first once it lands, and don't redo them.)

**Things a newcomer trips on:**
- `etc/lean-check.py` returns once the *edited* declaration checks. Run it again with `-a` before
  relying on a file.
- The worktree-isolated shell refuses commands that pass variables to `sed` or to version-control
  tools. Use plain commands, absolute paths, and Python scripts in a file for edits.
- `wp_take_receipt` needs a `FuncResolve` or `MethodResolve` in evaluation position, but `wp_auto`
  often resolves methods statically. Then take the receipt by hand: `wp_bind (App (Val (GoInstruction
  (StructFieldRef _ _))) (Val _))`, or the same with `GoOp`, then `wp_go_step_receipt'`. Its `hv`
  for a pair value is `rfl`.
- Track B works on the storage contract (`raft-unified-storage2`). Ask the coordinator before
  touching `readySnap`, `readyRest`, `Advance`, `StartNode`, `RestartNode` or the storage specs.
- Any new ghost state in a public spec is escalated before it is built on.

## Machinery (the map of the two modes, 2026-10-28)

- Mode: `RaftNames.reDyn` (`none` static), `reNoSnap`, `reNoXfer`, `reTracked` (static), `reSnapOkRaw`
  (`Protocol/Ghost.lean`); `RNMode` (`ApiVocab.lean:151`); `GMode` (`StepGhostMode.lean:46`);
  `StaticNames`/`DynNames` (`InvApi.lean:655`, `InvApiDyn.lean:197`).
- Dynamic-mode exclusions of snapshots: `DynNames.reNoSnap = true`; `snapshotCert` needs `reNoSnap =
  false` (`InvApi.lean:1399`); `storCap 1`; `ownRaftGhost_alloc_core`'s `ns` only with a non-empty
  log (`Protocol/Facts.lean:1193`; it allows `ns = false` with any log, the dynamic allocation passes
  `true`). (Lifted in U3: `DynNoSnap`, `"%Hsnap"`'s dynamic arm, `md.isDyn = false` at
  `MsgStorageAppendResp`, `GMode.Pre` at `MsgStorageApplyResp`; in U3d the node's `runCfg`/`readyData`.)
- Automatic leave excluded: `m'.autoLeave = false` (`node__ApplyConfChange`), `DynCCPreOp`, a dynamic
  snapshot's `ConfState` at `RawNode.Advance` (U3c), and
  `c.autoLeave → role ≠ leader` in `raft.appliedTo`, `appliedSnap`, `raft.Step`.

## Track C log (kvreconf)

- 2026-10-29: the leaf layer (pure model, porcupine model, encodings, maps, hashes, random helpers)
  specified and proved; `validConf.spec` stated over `ConfOk` (the rule's `Rule.lean`). Minor: kv's
  `foldl_histStep_opsOf` follows `opsOf`'s new filter (an empty `ConfChangeV2` has no client datum).
  Raft-side needs sent to the coordinator (`notes/decisions.md`, "Track C: kvreconf").
- 2026-10-29 (the coordinator's answers): every replica starts by `RestartNode` on a `Storage` whose
  `InitialState` answers the bootstrap `ConfState` (founders as newcomers; the `boot == nil` branch
  gone): **kvreconf no longer exercises `StartNode`** (raft's API has only the empty-log decision
  cluster). Quick tests and 3 rounds of `kvreconfcheck` pass. Hypotheses until tracks A/B land them,
  under the frozen names: `committed_confDecodes` (A), `Membership.applyChange_asV2` (B), the stopped
  answers and `Stop` with `nodeLive` (A, U9a); track B's approved storage hold mark and
  `applyGo`/`Restorable` to be used as they land.
- 2026-10-29: `RaftAssume` (one record, the frozen names; instantiated once in `Link.lean` when tracks
  A/B land the real ones) and `ConfStep` (proved). Next: the store's invariant (`Defs`: the client
  history over `ownCommittedOps`, the snapshot registry `ownSnapsMade` with `StateEnc` data, the
  `confPolicy`, the storage registry), then the run loop over today's `unifiedSpec`s.
- 2026-10-29 (checkpoint for a fresh agent): merged `origin/raft-unified-storage` (track B's client
  confchange API). Proved: `validConf` (over `ConfchangeApi`'s apiSpecs, `RaftLink.*_api` at link
  time; premises `m.Restorable`, `enterJointOf cc.transition |cc.changes| ≠ none`), `Replica.applyOp`
  (spec: the applier's `repOwn` at `ap` to `ap ++ [e]`, index field unchanged; the waiter answered with
  `waitP`). `Defs`: the replicated state split between the applier (`repOwn`, the store's map whole,
  halves of `applied`/`cs`/`index` and of the applied table, with the precise facts) and the lock
  (`repShared`: the other halves; the table some committed prefix's, for `propose`); `Halves.lean`
  combines/splits a map's halves; `PureLemmas.lean` (kv's applied-table lemmas, `hist_skip`,
  `hist_insert`, `logHist_snoc`). Next, in order: (1) `kvCore` needs the committed conf entries'
  shape (each decodes, through `MarshalsConfChange`, to a change with a defined transition: what
  `Reconfigure`'s `randomChange` proposes; raft's automatic leave is dropped by `opsOf` and decodes by
  `ccDecodeV2_nil`) -- `validConf`'s second premise, `applyEntry`'s decode (`committed_confDecodes`,
  `RaftAssume`); (2) `applyConf` (`validConf`, then `kvr_confAt_conf` for the decision, then
  `node.ApplyConfChange.unifiedSpec` or `RaftAssume.ApplyConfChange_stoppedSpec`; `r.cs` written with
  both halves); (3) `applyEntry` (dispatch, `proto.Unmarshal` specs, `r.index` moved with both
  halves); (4) `install`, `answer`, `maybeSnapshot` (`snapshotCert_make` over `kvrSnapInv`,
  `CreateSnapshot.unifiedSpec`), `maybeCompact` (storage specs: the hold mark is still a `RaftAssume`
  item, approved shapes); (5) `Replica.run`.

- 2026-10-29 (second track C agent): the invariant gap closed: `kvCore` records that every committed
  requested conf entry is `ConfShaped` (decodes, transition defined: `Rule.lean`), and
  `confShaped_of_ops` extends it to every committed conf entry (raft's automatic leaves outside `opsOf`,
  `ccDecodeV2_nil`; no bootstrap log), so `committed_confDecodes` left `RaftAssume` (the coordinator
  agreed; `committed_emptyV2_joint` not needed either). **Go change** (coordinator-approved, from track
  A's U9a analysis): `Replica.stop` closes `stopc`, waits for `run` and `ticker` to return
  (`runDone`/`tickDone`, buffered, one value each), and only then stops the node; so the applier never
  meets a stopped node: it holds a fraction of `nodeLive` and refutes every stopped answer
  (`nodeLive_stopped`); `RaftAssume` has no stopped-node triples (`ApplyConfChange_spec`: K9 + U5 form,
  stopped disjunct `⌜csp = null⌝ ∗ nodeStopped`); `repOwn`/`appNode` lost their stopped cases. Go tests
  and `-race` pass. Proved: `Stats.add` (`isCounter`/`isStats`, `Stats.lean`), `Replica.applyConf`
  (`conf_reject`/`wp_conf_apply`, `ApplyConfLemmas.lean`), `Replica.applyEntry` (`EntryLemmas.lean`;
  the `panic` refuted by `rkv_confShaped`), `ReadLemmas.lean` (`kvr_read_minted`; `MintOk` now bounds
  a read key's length). Stated: `Replica.answer.spec`. RaftAssume still stands in for: `nodeLive`/
  `nodeStopped`/`Stop` (U9a), `ApplyConfChange_spec` (U5 + K9; U5 is on raft-unified, merge allowed),
  and, to come: `Advance_spec` (running post only, U5 premises: the loop holds `nodeLive`), RestartNode
  on the wrapper storage with `σ.hd = W64 0` (U8), the storage-wrapper law, the storage hold-mark
  specs, U7's message shapes (Propose/msgCredits being redesigned: do not build on them yet). Next:
  `answer` (kv's proof, with `kvr_read_minted`), `install`, then the storage ones and `run`.
- 2026-10-29 (checkpoint, second track C agent, context nearly full; last commit `c077a7058e`):
  proved since the entry above: `Replica.answer` (kv's, the lock held across the loop) and
  `Replica.install` (spec: the snapshot's maps for a committed `L` of the metadata's index, its
  `ConfState` cloned, `confAt |L| mL`; the covered waiters answered over `wp_map_for_range_mut`).
  The applier's interface now: `repOwn γr r ap idx csp m mA A` (no stopped case), `appNode γr n l k m`
  (the node's view), `RA.nodeLive n γ N q` threaded through `applyConf`/`applyEntry`; `isReplica`
  (persistent fields, `isStats`, `kvrCluster`, the lock). Not yet in `isReplica`: `tick`, `stopc`,
  `runDone`/`tickDone` (the new Go fields; the run loop's exit hands its `nodeLive` fraction to `stop`
  through `runDone`, a buffered channel: a `Handoff` like the waiters'). **Next, in order**: (1) state in
  `RaftAssume` `Advance_spec` (today's `node.Advance.unifiedSpec` without the snapshot loan's
  `AutoLeave' = false` premise, running post only; the coordinator's answer on its stopped case is
  pending, see the messages: track A cannot give storage facts on a stopped node, which the
  stop-after-loop Go change makes moot for `run`), the Ready receive (today's `node.wp_readyRecv`
  suffices), RestartNode on the wrapper storage with `σ.hd = W64 0` (U8, when track B lands; Propose
  and `msgCredits_intro` are being redesigned: wait for the frozen shape); (2) the storage: the
  wrapper's methods (`Storage.InitialState`, `Storage.Snapshot`, the promoted `MemoryStorage` ones)
  and `maybeSnapshot` (`snapshotCert_make` over `kvrSnapInv`, `CreateSnapshot.unifiedSpec` from the
  hold: track B's shapes), `maybeCompact`; (3) `Replica.run` (kv's `KV__run.lean` as the model; the
  `select` on `Ready()`/`stopc`); then `propose`, `read`, `conf`, `contents`, `stop`, `ticker`, the
  cluster's functions, `newReplica`, `Link.lean`, `kvreconf_porcupine_safe`, `Results.lean`.

## raft-final: phases 0 and 1 (2026-10-29, branch `raft-final`)

The design is `raft-gap-design.md` (the coordinator's scratch, with its "Amendments after review 1",
A1-A10) and its review `invariant-design-review-1.md`; the user's decision of 2026-10-29 puts K5 back
in (overriding A9).

### Phase 0 (done)

- `raft-final` from `origin/raft-unified` (`87bae2abb4`), `origin/raft-unified-storage2` merged
  (`af6d445ae2`; textual conflicts only in `raft__maybeSendSnapshot`/`raft__maybeSendAppend`, where
  U7 (ii)'s term premise stays and S2's `ns` premise goes, and the notes). Raft's level builds after
  the merge (raft.Step, newRaft, getStatus, getProgressCopy, InvRawnode, MemstorageInstance).
- Track B's WIP patches re-applied (`7e2544e25d`): both apply cleanly (`step4-node-wip.patch`,
  `step4-boot-newLogWithSize.patch`).
- U9 deletions (`93992bc951`): the static and dynamic API families and their laws (the design's §1f
  list), `StartNode`'s spec and proof (A5: none until the server's repair, U10), the unified specs
  renamed `.spec`, `cluster_alloc_dec` renamed `cluster_alloc`. The trap: `InvApiDyn.lean` became
  `InvApiView.lean` (its membership and view sections, `nodeConfig`, `deliveredLogLb` and their laws,
  kept; its dynamic section deleted) -- deviation: renamed in place rather than merged into
  `InvApi.lean` (3221 lines; the view section needs `CCApplyC`/`SnapConf`).

### Phase 1 statements: public changes vs the frozen designs

Read the regenerated `interface/` (`etc/gen-interface.py etc/api/raft.txt`) for the exact text.

The node API (`InvNode`, `InvNodeRule`, the `Spec/node__*` files):
- **K5** (the user's decision, overriding A9): `nodeErrS n γ N cd err` (`nil`, `ErrStopped` with
  `nodeStopped n γ N`, or the context's) and `propErrS` (`nodeErrS ∨ stepErr`), with
  `nodeErrS_nodeErr`/`propErrS_propErr` back to the old ones; the posts of `node.Step`,
  `ProposeConfChange`, `ReadIndex`, `Campaign`, `ForgetLeader` are `nodeErrS`, `Propose`'s stopped
  disjunct `errStopped err ∗ nodeStopped n γ N`. The methods that return unit (`Tick`,
  `TransferLeadership`, `ReportSnapshot`, `ReportUnreachable`) have no stopped answer to carry it
  (C12 §3's list: "→ unit"). Raw level: `nodeErrRaw γn`/`propErrRaw γn` (`InvNodeChan`) in
  `node.step`, `stepWait`, `stepWithWaitOption`.
- `isNode` (sealed body) gains `nodeTabOk γ id γn` and `rdPool γ N` (design §2.8; deviation: not
  `isClusterU`, which lives above `InvApi` in the import order). (Step 1, F1 of the statements'
  review: not minor -- without `UniNames` neither `sentMsg_shape`'s `MsgSnap` bound nor
  `stepIn_intro` is provable; both bodies now end with `⌜UniNames γ N⌝`, "Spec changes during
  raft-final".)
- `bootStorage γ id st hs csm Q`; no `memStorage_bootStorage` law (design P7): a bare
  `MemoryStorage`'s `InitialState` answers the empty `ConfState` (`memSnapEmpty`), while
  `RestartNode` needs the voters' (`csm.Voters' = vs`, non-empty), so only a wrapper (kvreconf's,
  whose `InitialState` answers `c0`) can give the bundle: the client's, with its local storage
  instance (A6).
- `stepIn_intro`: `st.msg.To' = id → sentMsg ∗ msgPtsC … ∗ msgCredits ⊢ |==> stepIn` (no `NetMsgOk`,
  no transfer exclusion, no `MsgSnap` index premise: C12's form).
- New laws: `sentMsg_shape : sentMsg ⊢ ⌜SentMsgShape st ∧ (MsgSnap → ∃ sv, snap = some sv ∧ index <
  2^61)⌝` (C12; the bound from `snapshotValid`, A10), `msgCredits_intro : Type ≠ MsgProp → ⊢ |==>
  msgCredits` (S1), `readyRest_ceInBatch` (A2: a `Ready` without a snapshot, its committed entries at
  or past the batch's first index are the batch's), `snapshotCert_valid` (WIP's: a `readySnap`
  certificate, index in `(0, 2^61)`, gives `snapshotValid`).
- `msgCredits_copy` without its `MsgProp` premise (S1 F1).
- `node.ReadIndex.spec` without `readCredit γ`; `node.TransferLeadership.spec` without
  `leaderTransferOn γ N`; `cluster_alloc` (was `cluster_alloc_dec`) without `readCredits γ (2^64-2)`
  and `leaderTransferOn γ N` in its post.
- `node.Advance.spec`: `skippedIn` only after a `Ready` without a snapshot (A1, review 1's H1), inside
  the existing `match L`.
- `RestartNode.spec`: `bootStorage γ id st hs csm Q` with a client frame `Q` returned in the post (A3,
  H3).
- `MemoryStorage.Append.spec`: an empty batch takes and gives no range (A4, M2).
- New module `MemstorageApi` (importable): `memStorJ γ id`, `memStorInv ms γs γ id`,
  `memStorInv_alloc`, `memStorage_isStorage` (P7's; no wrapper law, A6).
- `NetMsgOk` internal (A7): moved to `NetMsgOk.lean` (not importable), its transfer clause admitting
  a stamped request to the node; `NetMsgOk.of_sent` replaced by `NetMsgOk.of_shape`.
- `isRaftMsg` (`ApiVocab`, exposed): `⌜SentMsgShape st⌝ ∗ (msgAbs, isMessageC) ∗ msgDat ∗ ⌜AppFrom⌝ ∗
  □ (stamped `MsgTransferLeader` → isLeader To Term)` (was the modes' clauses).
- `readySnap`/`readyRest`: WIP's storage part (unchanged by phase 1 but now built).
- Deleted with U9 (§1f), and also: `NodeNames.snapIn`, `readyDataL_none`, `readyP_none`, `reqWit_none`,
  `node_ready_receive_ns`, `readyP_take_ns` (the no-snapshot clients' lemmas), `setupNode` (only
  `StartNode` used it; `RawNode.Bootstrap` kept), `ConfChangeDecoder`.

Internal statements (raft's level, the RawNode, the node loop):
- `NGhost.xw` (the stamped transfer requests' `(To, Term)`), `NGhost.xf`/`bt` deleted; `XfOk` in its
  final form (§2.2: every queued message `SentMsgShape` and `AppFrom`, a stamped `MsgTransferLeader`
  recorded in `xw`, leader or candidate ⇒ term ≠ 0), with `XfOk.nil/of_fields/term_le/role/xw_insert/
  snoc/resps`, `ownRaftPhysC_term_nz` (was `ownRaftPhysC_xf`), `ownRaftPhysC_xw_record`;
  `raft.wp_store_stateC` takes `(ro = leader ∨ candidate) → s.term ≠ 0` (a default for the other
  roles); `wp_store_leadTransferee_toC` without `xf`.
- `Protocol/LeadWit.lean` (new): `leadW`, `leadW_none`, `leadW_eq`, `leadW_stepC` (deviation: over
  `StepC`, which `StepCD` and `StepCDS` both carry, rather than both `StepR` and `StepC`).
- `ghostRest = ⌜NsLink⌝ ∗ ghostRestM ∗ certLink ∗ leadW ∗ xfW` (the new conjuncts last, so that the
  patterns that bind the tail persistently still apply); `ownStepGhost_lead`, `ownStepGhost_xferRefute`,
  `ownStepGhost_xw_record`; `ownStepGhost_dyn` with the tail `(certLink ∗ leadW ∗ xfW)`.
- `raft.send`'s clause (c): `MsgTransferLeader → (m.To', s.term) ∈ s.gh.xw` (was `xf = false`);
  `stepFollower`: `lead ≠ 0 → (lead, term) ∈ xw` (A8); `stepLeader`, `raft.sendTimeoutNow`,
  `wp_stepLeader_transfer`, `RawNode.TransferLeader`: no transfer-mode premise; `RestMsgOk`'s transfer
  clause `ents = [] ∧ ctx = []` and `raft.Step.spec`'s new `"#Hxfer"` witness; `RawNode.Step.spec`:
  `"#Hxfer"`, no `reNoXfer`/`reNoSnap` premises; `NetMsgOk.restMsgOk`, `NetMsgOk.raftStep` without
  `Hxo`.
- `RawNode.Advance.spec`'s A1 only at `rs.slent = none` (A1); `runCfgLoan` without A1;
  `advanceP`'s A1 under `L = none`.
- `RawNode.Ready.spec`'s post: WIP's hand-out (`readyOut rs.storage rs.sn`, `ceFrozen`, `dlvKeysAt`).
- `newRaft.spec`, `NewRawNode.spec`: over the boot bundle (U8 v2's decision (B)): a frame `R`,
  `FirstIndex`/`LastIndex` triples, an `InitialState` triple whose post makes raft's view of a fresh
  storage and gives back `R'`.
- `netP`: the transfer witness in place of `reNoXfer`/`snapIn`; `netP_local` without `Hxt`;
  `readySnapData`, `runCfg`, `runCfgLoan`, `capAns` without `snapIn`/`reNoSnap`; `rawNodeFresh` without
  its `xf` parameter (its ghost state `{ sn := s.gh.sn }`).
- `rdPool γ N` (`InvApi`) and `rdPool_mint`; `isClusterU` with `rdPool`; `sentMsg` with `rdPool`;
  `msgCredits := stTks`; `stepIn` a `⊤` update after the receipt; `NodeOk` without `snapIn`;
  `nodeStopped` and `nodeDriver` without their static disjuncts.

Kept, deviations from the design's deletion list (each a mechanical removal with no statement
depending on its value):
- `NGhost.ns`, `NsLink` (now `s.gh.ns = γ.reNoSnap` only), `LogNsOk`, `NsCap`, `PrOkN`'s and
  `LogNsKeep`'s flag: the no-snapshot mode is pinned off by `NsCap`; removing the flag touches ~150
  sites of raft's level (P2's cleanup).
- `RaftNames.reNoXfer`/`reNoSnap` (protocol fields): no statement above the protocol reads them now;
  deleting them reopens `Protocol/Facts`' allocation proofs, which no track owns (phase 3 cleanup).
- `RNMode.static`/`GMode.static`/`StaticNames`/`CCShrink` (R3).

Not done in phase 1 (named for phase 2): `node.Step`'s and `node.ReadIndex`'s private raw specs
(`specRaw`, in their proof files: `(⧗ 1 ={⊤}=∗ stepP γn id ml)`, `(⧗ 1 ={⊤}=∗ rdCred γ.raft 1)`), and
the `nodeErrRaw`/`propErrRaw` posts of the other raw specs (`node.Propose.specRaw`, ...), which are
private to their proof files and change with their proofs (P5).

### Phase 1 sorries (all to be gone by the end of phase 2)

150 live `sorry`s in 76 files of raft's tree (at `93992bc951`, the end of phase 0, there were none;
phase 1's count, 152, included two inside `PHASE1-OLD` comments, `InvRaftPhys.lean`'s `XfOk.xw_insert` and
`ownRaftPhysC_xw_record`, each listed twice below), by
file (`P/` = `Proof/go_etcd_io/raft/v3/`), the declaration each is in:

- `P/InvAdvance.lean` (1): `advance_complete`
- `P/InvApi.lean` (10): `rdPool_mint`, `dlvLb_names`, `nodeRunning_stopped_impl`, `sentMsg_snapshot_impl`, `api_sentSnapCert`, `sentMsg_appFrom_impl`, `api_msg`, `readyRecv_open`, `node_ready_recvAu`, `stepIn_intro_impl`
- `P/InvApiDec.lean` (1): `snapshotCert_make_impl`
- `P/InvApiDecAlloc.lean` (1): `cluster_alloc_dec_impl`
- `P/InvApiView.lean` (4): `nodeDriver_deliveredLogLb_impl`, `deliveredLogLb_mono_impl`, `msgCredits_copy_impl`, `sentMsg_replaceSnapshot_impl`
- `P/InvBoot.lean` (1): `rawNodeFresh_intro`
- `P/InvNode.lean` (4): `sentMsg_shape`, `msgCredits_intro`, `readyRest_ceInBatch`, `msgCredits_copy`
- `P/InvNodeChan.lean` (5): `netP_local`, `netP_split`, `runCfg_congr`, `node_ready_receive`, `readyP_take`
- `P/InvNodeRule.lean` (1): `snapshotCert_valid`
- `P/InvNodeRun.lean` (13): `ownRawNodeReady_abandon_keep`, `wp_rn_raft_Step_net`, `wp_rn_raft_Step_prop`, `wp_applyConf_dyn`, `rawNode_applyCC_reseal`, `headRest_snapIn`, `headRest_step`, `runCfg_confc`, `runCfg_extend`, `runCfg_snap`, `runCfg_a1`, `runCfgR_a1`, `runCfg_advance`
- `P/InvNodeRunHup.lean` (1): `wp_rn_raft_Step_hup`
- `P/InvRaftPhys.lean` (8): `XfOk.resps`, `XfOk.term_le`, `XfOk.xw_insert`, `XfOk.xw_insert`, `XfOk.snoc`, `ownRaftPhysC_xw_record`, `ownRaftPhysC_xw_record`, `raft.wp_store_stateC`
- `P/InvRawnode.lean` (6): `NetMsgOk.restMsgOk`, `NetMsgOk.raftStep`, `ownRawNode_static_open`, `ownRawNode_intro_static`, `ownRaftPhysC_nsOut`, `ownRawNode_term_tc`
- `P/InvRawnodeReady.lean` (9): `outboxRelP_isRaftMsg`, `isRaftMsg_isMessage`, `ownRawNodeReady_abandon`, `ownRaftLog_certify_list`, `ownRaftLog_rdy_out`, `ownRawNodeReady_loanLast`, `ownRawNodeReady_handout`, `ownRawNodeIdle_facts`, `ownRawNodeIdle_ready`
- `P/LemmasNodeR.lean` (1): `stepP_split`
- `P/MemoryStorage__Append.lean` (1): `MemoryStorage.Append.wp_proof`
- `P/MemstorageApi.lean` (2): `memStorInv_alloc`, `memStorage_isStorage`
- `P/NetMsgOk.lean` (1): `NetMsgOk.of_shape`
- `P/NewRawNode.lean` (1): `NewRawNode.wp_proof`
- `P/RawNode__Advance.lean` (3): `wp_step_pending`, `wp_step_snapack`, `RawNode.Advance.wp_proof`
- `P/RawNode__Bootstrap.lean` (1): `RawNode.Bootstrap.wp_proof`
- `P/RawNode__Campaign.lean` (1): `RawNode.Campaign.wp_proof`
- `P/RawNode__ForgetLeader.lean` (1): `RawNode.ForgetLeader.wp_proof`
- `P/RawNode__Propose.lean` (1): `RawNode.Propose.wp_proof`
- `P/RawNode__ProposeConfChange.lean` (1): `RawNode.ProposeConfChange.wp_proof`
- `P/RawNode__ReadIndex.lean` (1): `RawNode.ReadIndex.wp_proof`
- `P/RawNode__Ready.lean` (1): `RawNode.Ready.wp_proof`
- `P/RawNode__ReportSnapshot.lean` (1): `RawNode.ReportSnapshot.wp_proof`
- `P/RawNode__ReportUnreachable.lean` (1): `RawNode.ReportUnreachable.wp_proof`
- `P/RawNode__Step.lean` (1): `RawNode.Step.wp_proof`
- `P/RawNode__Tick.lean` (1): `RawNode.Tick.wp_proof`
- `P/RawNode__TransferLeader.lean` (1): `RawNode.TransferLeader.wp_proof`
- `P/RawNode__acceptReady.lean` (2): `rdyLog_true`, `RawNode.acceptReady.wp_proof`
- `P/RawNode__readyWithoutAccept.lean` (1): `RawNode.readyWithoutAccept.wp_proof`
- `P/RestartNode.lean` (2): `RestartNode.wp_raw`, `wp_RestartNode_impl`
- `P/StepGhostMode.lean` (8): `ghostRest_certLink`, `ownStepGhost_lead`, `ownStepGhost_xferRefute`, `ownStepGhost_xw_record`, `ghost_stepCD`, `ownStepGhost_congr`, `ghostRest_keep`, `ghost_stepCDS`
- `P/newRaft.lean` (1): `newRaft.wp_proof`
- `P/node__Advance.lean` (2): `node.Advance.wp_raw`, `node.wp_Advance_impl`
- `P/node__ApplyConfChange.lean` (2): `node.ApplyConfChange.wp_raw`, `node.wp_ApplyConfChange_impl`
- `P/node__Campaign.lean` (2): `node.Campaign.wp_raw`, `node.wp_Campaign_impl`
- `P/node__ForgetLeader.lean` (2): `node.ForgetLeader.wp_raw`, `node.wp_ForgetLeader_impl`
- `P/node__Propose.lean` (2): `node.Propose.wp_raw`, `node.wp_Propose_impl`
- `P/node__ProposeConfChange.lean` (2): `node.ProposeConfChange.wp_raw`, `node.wp_ProposeConfChange_impl`
- `P/node__ReadIndex.lean` (2): `node.ReadIndex.wp_raw`, `node.wp_ReadIndex_impl`
- `P/node__ReportSnapshot.lean` (1): `node.ReportSnapshot.wp_raw`
- `P/node__ReportUnreachable.lean` (1): `node.ReportUnreachable.wp_raw`
- `P/node__Step.lean` (2): `node.Step.wp_raw`, `node.wp_Step_impl`
- `P/node__Stop.lean` (1): `node.wp_Stop_impl`
- `P/node__TransferLeadership.lean` (2): `node.TransferLeadership.wp_raw`, `node.wp_TransferLeadership_impl`
- `P/node__run.lean` (1): `node.run.wp_proof`
- `P/node__stepWithWaitOption.lean` (1): `node.stepWithWaitOption.wp_proof`
- `P/raft__Step.lean` (1): `raft.Step.wp_proof`
- `P/raft__becomeCandidate.lean` (1): `raft.becomeCandidate.wp_proof`
- `P/raft__becomeLeader.lean` (1): `wp_store_state_leader`
- `P/raft__send.lean` (1): `raft.send.wp_proof`
- `P/raft__sendTimeoutNow.lean` (1): `raft.sendTimeoutNow.wp_proof`
- `P/raft__tickElection.lean` (1): `raft.tickElection.wp_proof`
- `P/raft__tickHeartbeat.lean` (1): `raft.tickHeartbeat.wp_proof`
- `P/stepFollower.lean` (1): `stepFollower.wp_proof`
- `P/stepLeader.lean` (1): `stepLeader.wp_proof`
- `P/Protocol/LeadWit.lean` (1): `leadW_stepC`
- `P/raft__Step/Base.lean` (2): `ghost_step_static0`, `ghost_step_snapack`
- `P/raft__Step/MsgAppResp_eq.lean` (1): `wp_Step_MsgAppResp_eq`
- `P/raft__Step/MsgApp_eq.lean` (1): `wp_Step_MsgApp_eq`
- `P/raft__Step/MsgBeat.lean` (1): `wp_Step_MsgBeat`
- `P/raft__Step/MsgCheckQuorum.lean` (1): `wp_Step_MsgCheckQuorum`
- `P/raft__Step/MsgHeartbeatResp_eq.lean` (1): `wp_Step_MsgHeartbeatResp_eq`
- `P/raft__Step/MsgHeartbeat_eq.lean` (1): `wp_Step_MsgHeartbeat_eq`
- `P/raft__Step/MsgPreVoteResp_eq.lean` (1): `wp_Step_MsgPreVoteResp_eq`
- `P/raft__Step/MsgPreVoteResp_gt.lean` (1): `wp_Step_MsgPreVoteResp_gt`
- `P/raft__Step/MsgProp.lean` (1): `wp_Step_MsgProp`
- `P/raft__Step/MsgReadIndex.lean` (1): `wp_Step_MsgReadIndex`
- `P/raft__Step/MsgReadIndexResp.lean` (1): `wp_Step_MsgReadIndexResp`
- `P/raft__Step/MsgRest.lean` (3): `wp_Step_MsgLocal`, `wp_Step_MsgTransferLeader`, `wp_Step_MsgTimeoutNow`
- `P/raft__Step/MsgVoteResp.lean` (1): `wp_Step_MsgVoteResp`
- `P/stepLeader/Rest.lean` (2): `wp_stepLeader_transfer`, `wp_stepLeader_appresp`

### Spec changes during raft-final (old → new, why)

Step 1, the statement fixes after the review `phase1-statements-review.md` (2026-10-29):
- **F1** `isNode`'s and `sentMsg`'s sealed bodies end with `⌜UniNames γ N⌝` (no public change). Why:
  `sentMsg_shape`'s `MsgSnap` bound comes from `snapAtOk`'s `SnapListsOk`, which only holds with the
  registry on (`reSnapReg ≠ none`, `UniNames`' `ModeDec`); `stepIn_intro` needs the same bound for
  `raft.Step`'s `#Hsnap`. `cfgOf`/`memOf`/`stOf`/`stOf_cfg`/`memValid` (from `InvApiView`), `noDec`
  (from `DecFold`), `DecNames`/`ModeDec`/`ModeDec.mode`/`ModeDec.uniq`/`cfgOf_inj`/`UniNames` (from
  `InvApiDec`) moved into `InvApi.lean` (section `uninames`, after `Cluster`); `DecNames` states
  `memValid c0` (the sealed `Membership.Valid` lives above, in `InvNode`; `ModeDec.valid` stays in
  `InvApiDec` with its `c0.Valid` type); `Membership.ids` moved from `ConfRule` to `NodeApiVocab`
  (both importable; the name is unchanged).
- **F2** `etc/api-check.py etc/api/raft.txt --check` passes: `appendRight`, `appendReceipt`,
  `storFloor`, `storGiven` (and their instances) moved from `InvStorageLaws` (internal) into
  `InvStorage` (importable); `InvRaftlog` imports `InvStorageLaws` privately (and `InvStorage`
  publicly), `InvReadylog`/`InvRawnodeReady` import it privately; `LemmasEnts` listed importable
  (`LemmasMemstorage` re-exports it for kv); `StepGhostMode` delisted (F4), `ApiVocab` imports its
  public imports instead (`StepLemmasR`, `RefinementDyn`, `InvStorage`).
- **F3** `Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState` listed importable (kvreconf's wrapper
  calls it inside `bootStorage`'s `InitialState` triple).
- **F4** internal now: `StepGhostMode` (`ghostRest`, `leadW`'s use, `xfW`, `ownStepGhost_lead`/
  `_xferRefute`/`_xw_record`) is no longer importable; `Protocol.LeadWit` stays unlisted;
  `dlvKeysAt`/`dlvKeys` and their lemmas moved from `ApiVocab` (importable) to `InvRawnodeReady`
  (internal). **Not done: `NGhost.xw`** -- a field of `NGhost` in `Defs`, which importable
  modules (`InvRaftlog`, `InvReadylog`, `StepLemmas*`, `SpecResults`, `ApiVocab`, `Spec.Api`) state
  things over; hiding one field means moving `NGhost`/`NState` out of the importable vocabulary, the
  "Debt" group's cleanup (phase 3 or later). The coordinator (2026-10-29): defer it to that cleanup
  (`NGhost` is internal vocabulary already exposed, not new client ghost state). **Debt list:** `NGhost.xw`
  (with `NGhost`/`NState` out of the importable modules).
- **F5** `node.Propose.spec`'s post is `propErrS n γ N cd err` (was the same disjunction spelled out:
  `nil ∨ ErrStopped ∗ nodeStopped ∨ ErrProposalDropped ∨ ctx`); one name for clients, with
  `propErrS_propErr` back to the old `propErr`.
- Minor: `bootStorage`'s triples without their explicit `□` (a triple is already `□ ∀ Φ`; the
  interface showed `□ □`); its docstring no longer names the deleted `memStorage_bootStorage`. New law
  `memStorFresh_compacted` (`InvMemstorage`): `memStorFresh ms γs ∗ memCompacted γs c ⊢ ⌜c = 0⌝ ∗
  memStorFresh ms γs`, so a wrapper's `FirstIndex` answers exactly `1`. Docstrings of `stepIn_intro`,
  `nodeRunning`, `nodeStopped`, `readyFits` brought up to date.
- Checked: the global `memStorageModel` instance coexists with a client's own `StorageModel`: with
  `[MemStorReg GF]` and a local `[inst : StorageModel GF]` in scope, `inferInstance = inst` by `rfl`
  (the local instance wins). A client that declares a second *global* instance would depend on
  declaration order; kvreconf's should be a section variable or a `local instance`.

### Phase 2: the tracks, file-disjoint (at most four at a time)

Every `sorry` above is in exactly one track's files. The old proof of a sorried body is kept below
it, in a comment `/- PHASE1-OLD … -/` (the starting point; the statement above it is the final one).
Waves: {P1+P2, P3a, P5, P7}, then {P3b, P4, P6}; each track checks against the fixed statements
(`etc/lean-check.py`) and only builds once the tracks below it are in.

| track | files |
|---|---|
| P1+P2 raft level | `Protocol/LeadWit`, `InvRaftPhys`, `StepGhostMode`, `raft__Step` and `raft__Step/*`, `raft__send`, `raft__sendTimeoutNow`, `stepFollower`, `stepLeader`, `stepLeader/Rest`, `raft__becomeCandidate`, `raft__becomeLeader`, `raft__tickElection`, `raft__tickHeartbeat` (and, as cleanup, `NGhost.ns`/`NsLink`/`LogNsOk`/`NsCap`/`PrOkN`'s flag) |
| P3a Ready side | `InvRawnodeReady`, `RawNode__readyWithoutAccept`, `RawNode__acceptReady`, `RawNode__Ready`, `LemmasReadyR` |
| P3b RawNode rest | `InvRawnode`, `NetMsgOk`, `RawNode__Advance`, `RawNode__Step`, `RawNode__Bootstrap`, `RawNode__{Campaign,ForgetLeader,Propose,ProposeConfChange,ReadIndex,ReportSnapshot,ReportUnreachable,Tick,TransferLeader}` |
| P4 node loop | `InvNodeChan`, `InvNodeRun`, `InvNodeRunHup`, `LemmasNodeR`, `node__run`, `InvAdvance`, `node__Advance`, `node__ApplyConfChange` |
| P5 node methods | `node__stepWithWaitOption`, `node__step`, `node__stepWait`, `node__Step`, `node__Propose`, `node__ProposeConfChange`, `node__ReadIndex`, `node__Campaign`, `node__ForgetLeader`, `node__TransferLeadership`, `node__Stop`, `node__ReportSnapshot`, `node__ReportUnreachable` (with their private `specRaw`s: `nodeErrRaw`, the receipts) |
| P6 API, allocation, restart | `InvApi`, `InvApiView`, `InvApiDec`, `InvApiDecAlloc`, `InvApiJoin`, `InvNode`, `InvNodeRule`, `InvBoot`, `newRaft`, `NewRawNode`, `RestartNode` |
| P7 MemoryStorage | `MemoryStorage__Append`, `MemstorageApi` |

`Link.lean` is generated (`etc/gen-link.py --raft`; phase 1 taught it to add `[StorageModel GF]`
when a callee's result takes it).


## kvreconf-final (2026-10-29, branch `kvreconf-final`, from `raft-unified-kvreconf` + `raft-final` 8f14f5df18)

The design: the coordinator's `kvreconf-gap-design.md` with the amendments of `raft-gap-design.md`
("Amendments after review 1") and `invariant-design-review-1.md` (scratch, job c8379647).

**Go changes** (tests and `-race` pass; `notes/decisions.md`, "kvreconf-final"):
- O6: `validConf` caps the configuration at `< 2^61` ids (`ConfOk` carries it), so a snapshot's
  conf-state lists sum below `2^62` (`snapshotValid`).
- F6/O8: `send`/`deliver` copy messages by hand (`copyMsg`: the field pointers shared, a fresh
  `Entries` slice of the same read-only entries, the snapshot by `proto.CloneSnapshot`, no
  `Responses`), not `proto.Clone` of `*raftpb.Message` (whose only `PbType` is the server's trusted
  wire model): no trust-base change (coordinator-approved). The duplicate is `copyMsg` of the owned
  copy (`copyMsg` reads at any fraction), so `deliver` keeps its shape.

**Structure.**
- `RaftAssume` retired: `applyConf` takes raft's `node.ApplyConfChange.spec`.
- `KvrStorage`/`KvrStorageApi` (the wrapper's registry `KvrStor`, `kvrStorageModel` as a `def`
  activated by `attribute [local instance]` in every file that needs it, never global; transport
  lemmas; `kvrJ`; `kvrStorage_isStorage`; `kvr_bootStorage` with frame
  `memStorMeta ∗ memStorInvP`; the promoted-method lemmas `Storage.wp_X`). Done, no `sorry`.
- `DefsCluster` (new predicates beside `Defs`' so the proved methods stay): `isReplicaR`/`isRep`,
  `repStop` (stop tokens), `runStart`, `frozenTo` (indexed by the delivered log, H4), `sendSpec`,
  `repKnown` (a `monoNat` bound on the next id instead of a replica map), `stopper`,
  `clusterLockInv`, `isClusterC`.
- Frozen interface statements (21 spec files): `run`, `newReplica`, `stop`, `conf`, `propose`,
  `read`, `do`/`Put`/`Get`/`Read`, `StartCluster` (allocates raft's cluster and the store's state),
  `Cluster.Stop`, `all` (with `own`: takes the stop tokens), `random`, `replica`, `randomMember`,
  `startNew`, `sender`, `tick`, `Reconfigure`, `Disrupt`. Each proof group writes its internal
  specs itself (spec-first).

**Proof groups** (helpers in this worktree): T1 storage (done); RUN (`run`, `maybeSnapshot`,
`maybeCompact`); CLIENT (`propose`, `read`, `conf`, `do`/`Put`/`Get`/`Read`, `ClientLemmas` with
`kvr_propAu`, `kvr_ccAu`); LIFE (`newReplica`, `ticker`, `stop`, `StartCluster`, `config`,
`startNew`, `all`, `random`, `replica`, `randomMember`, `tick`, `Stop`); to come: NET (`sender`,
`send`, `copyMsg`, `deliver`, `step`, `dropped`), RECONF (`randomID`, `randomChange`, `sleep`,
`Reconfigure`, `Disrupt`), TOP (`RandomOptions`, `RandomConfig`, `Run`, `Main`, `Link`,
`Adequacy`, `Results`).
Phase 2 (internal statement changes):
- `ownStepGhost_lead`, `ownStepGhost_xw_record` (`StepGhostMode`, internal): a premise
  `s.role ≠ .preCandidate` added (the coordinator approved it, 2026-10-29). Why: `toPState` zeroes `lead` at a pre-candidate, so `leadW`
  says nothing there.

- `ghostRest_keep` (internal): premise `(hro : s'.role = s.role := by rfl)` added. Why: `leadW` reads
  `toPState`'s lead, which a pre-candidate zeroes, so a phys `lead` equation is not enough.
- `outboxRelP_isRaftMsg`/`_isRaftMsgs`/`self_pending` (internal, P3a): `Hsent` (the `reNoXfer` mode's
  `SentMsgOk`) is replaced by XfOk's clauses: `SentMsgShape`, `AppFrom`, the stamped transfer's
  `∈ s.gh.xw`, and `xfW γ s`. `Hns` is kept (`qCert` still has its `reNoSnap` disjunct).

- `rdPool` (internal, `InvApi`): `⌜receiptBound GF ≤ 2^64 - 2⌝ ∗ inv …` (was the invariant alone);
  `rdPool_mint` without its `receiptBound` premise. Why: `node.ReadIndex.spec` has no such premise
  and `isNode` bounded nothing; `cluster_alloc` takes the premise, its allocation records it.

- `wp_store_state_leader` (private, `raft__becomeLeader`): premise `s.term ≠ 0` added (its caller
  passes `becomeLeader.spec`'s own). Why: `raft.wp_store_stateC` at `.leader` needs it now.
- P5's private raw specs (`node__*.lean`): `nodeErrRaw`/`propErrRaw` posts; `node.Step`'s raw spec takes
  `(⧗ 1 ={⊤}=∗ stepP γ id ml)`, `node.ReadIndex`'s `(⧗ 1 ={⊤}=∗ rdCred γ.raft 1)`;
  `ProposeConfChange`'s raw spec posts `nodeErrS` directly; `TransferLeadership`'s raw spec
  without `reNoXfer = false`. New lemma module `LemmasP5NodeErr.lean` (the raw errors' intros and the
  bridges `nodeErrRaw_nodeErrS`, `propErrRaw_propErrS`, `nodeStoppedRaw_nodeStopped`).

- New public laws (the coordinator's request, for kvreconf, 2026-10-29): `Membership.Valid.snapListsOk`
  (`InvNodeRule`): `m.Valid → confStateIs cs m → W64 0 ∉ m.ids → (∀ k ∈ m.learnersNext, k ∉
  m.voters) → GMap.size m.ids < 2^61 → uint.Z i < 2^61 → SnapListsOk ⟨⟨t, i⟩, cs.lists, m.autoLeave,
  d⟩`, and `Membership.Valid.snapListsOk'` (`ConfchangeApi`), the same law with `m.Restorable` in place
  of the two clauses. Deviation from the request: the requested statement lacked the `Restorable`
  premises, and without them it is false (`Valid` allows the id `0` and a staged learner that is an
  incoming voter, while `CSWf` excludes both).
- `raft.Step.spec`'s `%Hframe` (internal): `MsgTransferLeader` is excluded from `NetFrame`, with a
  clause of its own (`NetFrame s { s' with gh := s.gh }`, and `s'.gh` is `s.gh` but for `xw`). Why: the
  forward records `(lead, term)` in `s.gh.xw`, so `s'.gh = s.gh` fails.

- `raft.Step.spec` (internal, P2b): `%Hframe` with `m.Type' ≠ MsgTransferLeader →`, and a new conjunct
  `%Hxwframe` (`MsgTransferLeader → NetFrame s { s' with gh := s.gh } ∧ s'.gh = { s.gh with xw :=
  s'.gh.xw } ∧ xw grows`); `wp_Step_MsgTransferLeader`'s xw premise only at a follower with a leader
  (a pre-candidate's lead is hidden by `toPState`).
- `SdtTie` (internal, `InvRawnode`): `s.logst.dtk = sdtLen rs`, `sdtLen` = `l.dlv.length` while a loan
  `l` is out, else `delivered.length` (was `delivered.length` always, false after a snapshot `Ready`:
  the hand-out certifies `l.dlv`'s keys); `SdtTie.of_none`; `keep`/`ofRec`/`snap` keep the loan.

- P3a (internal): `outboxRelP_isRaftMsg`/`_isRaftMsgs`/`self_pending` take `(s : NState)`, XfOk's
  clauses 1-3 and `xfW γ s` (was `Hsent`/`Hrs`); `rdyLs`/`rdyLog_true`/`readyNstate` take `dk`
  (`rdyLog_true` was false with a loan: `lendLog` also sets `sg`); private lemmas `ownRaftLog_kcert`
  (`InvRawnodeReady`), `ghostRest_xfW` (`LemmasReadyR`).
- Requested by the coordinator for kvreconf (assigned to P6): `readyRest_indices` (`InvNode`), with a
  pure indices conjunct added to `readySnap none`'s body.

- Moved to the importable `InvPb` (the coordinator's request, for kvreconf): `csPts_combine_open`,
  `csOptA_combine`, `smPts_combine`, `smOpt_combine`, `ownSnapM_combine`, `snapOpt_combine` (were in
  the internal `InvRawnodeReady`); `msgOwn_combine` stays.

- `readySnap none` (public, InvNode and ApiImpl): a trailing pure conjunct, the batch's indices
  consecutive from its head and the committed entries at or past the batch's head the batch's
  (`readyRest_indices`, new, and `readyRest_ceInBatch` are its projections). Its sources (internal,
  P4): `readyData` (InvNodeChan) gets the same fact as its last conjunct, and `ownRawNodeReady` gets
  `"%Hcepre" ∷ ⌜es ≠ [] → ce <+: logCommittedEnts s.logst⌝` (from `readyWithoutAccept`'s `Hce`;
  guarded: `ownRawNodeIdle_ready` re-sends a stale `Ready` with `es = []`).

- `newRaft.spec` (internal): post gains `s.logst.dtk = 0`; `NewRawNode.spec` (internal): post gains
  `s.logst.sn = sn ∧ s.gh.sn = sn`; `rawNodeFresh`'s `%Hlog` gains `s.logst.dtk = 0`. Why: `RestartNode`
  needs `SdtTie` of the fresh node and the boot bundle's storage names, which the posts left out.

- P6 (internal): `api_sentSnapCert` takes `reNoSnap = false`; `api_msg`/`api_msgs` take `UniNames`,
  `rdPool` and no per-message `rdCred`; `RestartNode.specRaw` (private) takes the five configuration
  names and their resources from the wrapper; new `sentMsg_snap_bound`, `rawNodeFresh_intro_sn`.
- P4 (internal): `wp_rn_raft_Step_net` takes the transfer witness (no `Hxt`/`Hsnp`); A1 guarded by
  `rs.slent = none` also in `runCfgR_a1`, `runCfg_advance`, `advRet` (phase 1 missed them; false while a
  snapshot is lent); `readySnapData` gains `raftSnapCertD` of the lent snapshot; `leadW_applyCC`.
  Cleanup candidate: P4's `RNPv.step_xw`/`LoanOk.step_xw` and P3b's `LemmasP3bXw` overlap.
- Client repair note: `readySnap none`'s new trailing conjunct needs a binding in the server's and
  kv's destructurings (`InvRaftNode`, `SrvRaftLog`, `KV__run`).

- P3b (internal): `ownRawNode_static_open` also returns `leadW ∗ xfW`, `ownRawNode_intro_static` and
  `rawNode_applyCC_reseal` take them; `RawNode.Bootstrap.spec` takes `γ.reNoSnap = false` and posts `sn :=
  s.gh.sn`; new last conjunct of `SnpOk`, `SnpSg g ls := ls.lent = true → ∀ k, g.snp = some k → ls.sg ≤
  uint.nat k.sid.index'` (`SnpKeep` keeps `sg`; `of_fields` take `hsg := rfl`), for `RawNode.Advance`'s
  `ownRaftLog_absorb_snap`; `lendLog`/`lendView` set `sg := uint.nat prev.index'` (was `max sg …`, the
  same value: `ownStorage_sg`); `LemmasP3bXw.lean` (cleanup candidate, overlaps P4's `step_xw`).
- Phase 2 done at `9491b601ab`: raft's Link/Linked/Results/Api/MemstorageApi build, 0 live `sorry`s.

### Phase 2 progress (the lead's hand-off)

- Step 1 (statement fixes) pushed at `8f14f5df18`.
- Wave 1 started 2026-10-29 with four helpers in this worktree, under the common brief
  `/home/ubuntu/.claude-E/jobs/c8379647/tmp/phase2-brief.md`. P1+P2 is split in two:
  P2a = `InvRaftPhys`, `raft__send`, `raft__sendTimeoutNow`, `raft__become{Candidate,Leader}`,
  `raft__tick{Election,Heartbeat}`, `stepFollower`, `stepLeader`, `stepLeader/Rest`;
  P2b = `Protocol/LeadWit`, `StepGhostMode`, `raft__Step`, `raft__Step/*`; P3a as in the table;
  P5 together with P7. Done: P5+P7, P2a, P2b, P3a, P4, P6. P3b running. Then phase 3.

### kvreconf-final: the read path, for the logically atomic `Cluster.Read` (2026-10-30)

The user chose a logically atomic `Cluster.Read` spec (by prophecy), its spec to be designed and
signed off first; until then `Run`'s `opRead` branch is the single `sorry` of kvreconf's chain
(isolated in its own lemma in `Run.lean`). What the read path is today:

- **Go.** `Cluster.Read(key)` (cluster.go) loops `c.randomMember().read(key, opTimeout)` until one
  answers. `Replica.read` (kv.go) takes `r.mu`, bumps `r.nextRead` (stops at `maxSeq`), registers a
  buffered channel at `r.reads[seq]`, unlocks, calls `node.ReadIndex(ctx, readCtx(r.id, seq, key))`
  under a `WithTimeout` context, and waits on the channel or the timeout (then deletes its entry and
  tries the channel once more). The applier's `answer` (kv.go), after each Ready's committed entries,
  answers every pending `ReadState` whose `Index ≤ r.index` and whose context decodes to this
  replica: `ch <- r.kv[key]` (the store's map at the applied prefix `ap`).
- **Today's specs.** `Replica.read.spec`/`Cluster.Read.spec` (frozen, proved): from `kvLb γr L0` the
  answer is `kvFold L key` with `L0 <+: L` and `kvLb γr L`. Proof: `kvr_mint_read`
  (`ClientLemmas.lean`) mints the context at `(id, seq)` and registers it with raft by
  `readCtx_commit_after` with the trivial `Q` (`kvr_readAu`), giving `isReadCtx … c (fun _ => True)`
  and `readCtxAfter … c l0` (`l0` committed when the read starts). `answer` sends `readAns γr c v`
  (`Defs.lean`: a read state of `c` at `i`, a committed `ap` with `i ≤ |ap|`, `v = kvFold (logHist ap)
  key`), and `kvr_readAns_ok` turns `readCtxAfter ∗ readAns` into the lower-bound post.
- **Why it is not logically atomic as is.** The answer is the state at the moment the history was
  exactly `logHist ap`, which lies between the call and the return: the history grows one datum at a
  time (each commit appends at most one), from the history at the call (`|·| ≤ i ≤ |ap|`, `i` the
  read index, fixed after the call) to the history at the return (`ap` committed). But that moment is
  known only once the applier answers, after it: firing the client's AU needs a prophecy of `|logHist
  ap|` (or of the answer), resolved by the reader when the answer arrives (`primitive.NewProph` /
  `ResolveProph`: a Go change in `Replica.read`, or a ghost-only prophecy if the port has one), with
  the store invariant firing the pending read's AU at the commit that makes the history that long (or
  at once if it already is). Raft's `isReadCtx`'s `Q` (fired at raft's own read point, when the
  leader's commit index is fixed) is not the read's linearization point here: the applier answers at
  `r.index ≥ i`, possibly later.

### kvreconf-final: done (2026-10-30)

`kvreconf_porcupine_safe` builds with no `sorry` (`Results.lean`; STATUS has the axioms). Every
proof group finished: T1 storage, RUN/RUN2 (`run`, `maybeSnapshot`, `maybeCompact`), CLIENT,
LIFE, NET, RECONF, TOP (`RandomOptions`, `RandomConfig`, `Run`, `Main`, `Link`, `Adequacy`,
`AdequacyLinked`, `Results`), READ (the atomic `Cluster.Read`: `ReadSlot.lean`, gokv's
`trusted_proph`). Left: `etc/tcb-report.py --roots kvreconf` and a kvreconf TCB collection, once
the whole repository builds (after the clients' repair); merging into `lean` with the rest of the
raft-unified train.
  P5 together with P7. All tracks done (phase 2 complete at `9491b601ab`); phase 3 next. Then phase 3.

### Phase 3 (done 2026-10-30)

- `Link.lean` regenerated (`etc/gen-link.py --raft`): unchanged. `Linked` exports every `node` method
  and `MemoryStorage.{InitialState, CreateSnapshot, ApplySnapshot, Compact, Snapshot}` (review F3).
  `Results` also prints the axioms of `InvNode`'s, `InvNodeRule`'s, `MemstorageApi`'s and
  `InvMemstorage`'s laws. No result depends on `sorryAx`.
- `interface/` regenerated; `etc/api-check.py etc/api/raft.txt --check` passes; `gen-interface
  --check --layout`: 0 new layout violations.
- Axioms, read off `#print axioms` of all 415 printed results, against `etc/tcb-collections/raft.txt`:
  the baseline's 13, plus **`ccDecodeV2_nil`** (the expected one, user-approved). The type
  axioms of untranslated types are the same as before. `etc/tcb-report.py --collection … --check
  --update` is not run: it needs the whole repository built, and the clients are broken until the
  repair phase. Run it, with the user's go-ahead, once they build.

### Spec changes during the repair, raft (Stage R: R2, R3, R5; 2026-10-30, branch `repair`)

The approved items, as built (statements shown to the coordinator first,
`stageR-raft-statements.md`):
- **R2** `readyFits_intro : receiptBound GF + γ.bootLen ≤ 2^61 → ⊢ readyFits γ N` (`InvNode`), and
  `cluster_alloc`'s post gives `γ.bootLen = boot.length`. Deviation from "cluster_alloc gives
  readyFits": not unconditionally, since kvreconf allocates under `receiptBound ≤ 2^63` (its adequacy).
- **R3** `nodeConfig_confAt : nodeConfig n γ N v ⊢ nodeConfig n γ N v ∗ confAt γ v.applied v.membership`.
  `nodeConfig`'s sealed definition moved from `InvNode` to `InvNodeRule` and now holds `confAt` (the
  module cycle otherwise: `confAt` is defined after `InvNode`). No spec statement changed;
  `node.ApplyConfChange`'s proof derives `confAt (k+1) m'` over a new law, **`confAt_skipped`**
  (`isCommittedLogLb γ l ∗ confAt γ a m ∗ skippedIn γ l a b ⊢ confAt γ b m`, `a ≤ b ≤ |l|`), an
  addition beyond the approved list (pure consequence of `confAt_noConf`/`confAt_decided`).
- **R5** One `cluster_alloc N vs ctxs boot dup E` for both forms: premise `boot ≠ [] → BootLog vs ctxs
  boot`, taking `if boot = [] then emp else bootMarshal …`; the post's last conjunct
  `if boot = [] then joinAuth ∗ [∗] nodeFounder else isCommittedLogLb γ boot ∗ [∗] nodeBoot γ N vs ctxs
  id`; `ownCommittedOps γ boot`. New sealed `nodeBoot` (`InvApiBoot.lean`). The boot conf entries are
  not decided at allocation (the client decides them with `confDecide`; each `AddNode` of a voter is a
  no-op at the voters' membership). New `StartNode.spec` (importable), over `RestartNode`'s
  `bootStorage` at the empty conf state, `peersCtx`, `nodeBoot`; post as `RestartNode`'s plus the
  peers' slice. Internally `setupNode.spec` restored (raw) over the proved `RawNode.Bootstrap`.
  **Deviation (logged, coordinator informed):** the boot form gives no `joinAuth`: raft's protocol
  keeps the bootstrap log a prefix of every node's log (`Protocol/Ghost.lean`, `isCampK`,
  `isLeader_boot`), which a newcomer's `RestartNode` on an empty storage breaks; supporting joiners
  there needs that protocol invariant weakened.
- Internal: `allocOut` carries `isCommittedLogLb γ boot`; `cluster_alloc_dec_impl`'s post gives
  `reBoot.length = 0`. kvreconf's `StartCluster` call adapted (4 lines).
- `#print axioms wp_StartNode`: exactly `wp_RestartNode`'s; no `sorry`.
