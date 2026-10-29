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
4. **U9**: one spec per function; the old families deleted.

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
