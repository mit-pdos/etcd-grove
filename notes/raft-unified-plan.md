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
  following a restore. (2026-10-28: U3a, the model, and U3b, `raft.Step`'s two storage-response cases,
  done; U3c, the `RawNode`, and U3d, the node, left: `notes/decisions.md`, "Stages U2, U3".)
- **U4. Allocation without `reNoSnap`, joiners.** `ownRaftGhost_alloc_core` for a dynamic cluster with
  snapshots and an empty or bootstrap log; `joinAuth`; `RestartNode` from `γ.c0`; a joiner (empty log,
  configuration `c0`) in the protocol invariant beside the founders; pre-votes granted at term 0 with
  no `bootedCluster` premise (scope: newcomers start at `c0`, not on an empty `ConfState`).
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

## Machinery (the map of the two modes, 2026-10-28)

- Mode: `RaftNames.reDyn` (`none` static), `reNoSnap`, `reNoXfer`, `reTracked` (static), `reSnapOkRaw`
  (`Protocol/Ghost.lean`); `RNMode` (`ApiVocab.lean:151`); `GMode` (`StepGhostMode.lean:46`);
  `StaticNames`/`DynNames` (`InvApi.lean:655`, `InvApiDyn.lean:197`).
- Dynamic-mode exclusions of snapshots: `DynNames.reNoSnap = true`; `snapshotCert` needs `reNoSnap =
  false` (`InvApi.lean:1399`); `storCap 1`; `DynNoSnap` (`InvRawnode.lean:518`); `"%Hsnap"`
  (`InvRawnode.lean:1984`); `md.isDyn = false` at `MsgStorageAppendResp` (`raft__Step.lean:588`);
  `GMode.Pre` at `MsgStorageApplyResp` (`StepGhostMode.lean:63`); `ownRaftGhost_alloc_core`'s `ns` only
  with a non-empty log (`Protocol/Facts.lean:1193`).
- Automatic leave excluded: `m'.autoLeave = false` (`node__ApplyConfChange`), `DynCCPreOp`, and
  `c.autoLeave → role ≠ leader` in `raft.appliedTo`, `appliedSnap`, `raft.Step`.
