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
