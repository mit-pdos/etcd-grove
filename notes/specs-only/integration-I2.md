# Integration I2 (raft): report

Integration agent I2, 2026-11-09. Scope: `Spec/go_etcd_io/raft/` (v3's `Model`, `Api`, `ApiCore`,
`ApiLog` and specs; `tracker`, `quorum`, `confchange`, `raftpb`) and the snippets
`examples/specreq/{raftnode,raftcore,raftlog,raftconf,raftpb}/`. Batches R1, R2, R3, R4, 3h's raftpb
part.

## Build

- `etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3/raftpb Spec/go_etcd_io/raft/v3/tracker
  Spec/go_etcd_io/raft/v3/quorum Spec/go_etcd_io/raft/v3/confchange Spec/go_etcd_io/raft/v3`:
  **OK (350 modules)**, after all the changes below.
- The directories outside mine that import raft's vocabulary (`etcdserver`, `api/membership`,
  `api/rafthttp`, `api/snap`, `etcdserver/apply`, `etcdserver/read`, `storage`, `storage/wal`: 26
  modules import raft's `Model`/`Api` directly) were rebuilt with them: `Build completed
  successfully (2790 jobs)`, no error. The script's final `--no-build` check then reported them
  stale: other integration agents were editing files in those directories at the same time (`git
  status`), not a failure of these changes.
- Snippets: `cd examples && go vet ./specreq/raftnode/ ./specreq/raftpb/ ./specreq/raftconf/` clean;
  `gofmt -l` of all five directories (`raftcore`, `raftlog` are `//go:build ignore`) prints nothing.

## Provisional names resolved

Mechanism: raftpb's, the tracker's and quorum's names are **re-exported** (`export`) into R1's and
R3's namespaces under the old names, so every statement and every client file outside my
directories (`Raft.LogEntry`, `Raft.snapshotPts`, `Raft.HardState.empty`, ...) keeps resolving, to
one definition. R1's helpers on raftpb's types are declared in the `RaftPb` namespace (in R1's
`Model.lean`), so that dot notation finds them on the shared types.

| provisional | where | now |
|---|---|---|
| `LogEntry`, `HardState`(+`.empty`), `ConfState`(+`.empty`), `Snapshot`(+`.empty`), `ConfChangeV1`, `ConfChangeSingle`, `ConfChangeV2`, `ConfChangeI` (+`entryType`), `Msg`, raftpb's enumerations | R1 `Model.lean` (own structures) | `RaftPb.*`, exported |
| `decodeConfChange`, `bootEntryData` (opaque) | R1 `Model.lean` | `RaftPb.decodeConfChange` (a definition), `RaftPb.bootEntryData`, exported; `bootEntryData_decode.spec` kept (follows from `RaftPb.bootCC_facts`) |
| `Membership` (+`simple`, `empty`, `ids`, `isJoint`), opaque `Membership.Valid` | R1 `Model.lean` | `Tracker.Membership`, `Tracker.Membership.Valid`, exported |
| opaque `Membership.applyChange` | R1 `Model.lean` | defined: `.v1 cc ↦ ConfChange.changeV2 ⟨TransitionAuto, [⟨cc.type, cc.nodeId⟩]⟩`, `.v2 c ↦ changeV2 ⟨c.transition, c.changes⟩` |
| `ConfState.Is` | R1 `Model.lean` | `RaftPb.ConfState.Is := ConfChange.Lists` of the five fields (declared in R1's file) |
| `LogEntry.isConfChange/isFiller/isEmptyV2`, `Snapshot.isEmpty` | R1 `Model.lean` | moved to the `RaftPb` namespace (same file), for dot notation |
| `entriesRO`, `msgPts`, `hardStatePts`, `snapshotPts`, `confStatePts`, `confChangePts` (opaque) | R1 `Api.lean` | `RaftPb.*`, exported (with `entryRO`, `entryPtrs`); their persistence conjuncts dropped from R1's `persistent.spec` (raftpb's `raftpb_persistent`) |
| `entryPtrs`, `progressCopyOwn`, `trkResult` (opaque) | R2 `ApiCore.lean` | `RaftPb.entryPtrs` (exported); `progressCopyOwn` and `trkResult` defined over R4's `ownMap`/`progressValOwn`, `configOwn`/`progressMapOwn`/`TrackerOk` |
| `entryRO`, `jointConfigOwn` (opaque), `MajorityIdx`, `JointIdx`, `ConfState.Equiv` | R3 `ApiLog.lean` | `RaftPb.entryRO`, `RaftPb.ConfState.Equiv`, `Quorum.{jointConfigOwn, MajorityIdx, JointIdx}`, exported |
| `ccsPts` (opaque), `Single` (own structure), the enumerations | R4 `confchange/{Api,Model}.lean` | `RaftPb.ccsPts` (exported; a definition, splittable per element), `abbrev Single := RaftPb.ConfChangeSingle`, the enumerations raftpb's |
| `Raft.confStatePts`, `Raft.ConfState` | R4 `confchange/{Restore,toConfChangeSingle}`, `tracker/ProgressTracker__ConfState` | `RaftPb.confStatePts`, importing raftpb's `Api` instead of R1's |

**Left** (R1's own raft-struct predicates, not provisional for another batch): `softStateOpt`,
`readStatesRO`, `peersPts`, `statusOwn`. R1's enumerations that are raft's (`StateType`,
`SnapshotStatus`, `isLocalMsgType`, ...) stay R1's.

## Laws restated

- `Membership.applyChange_v1.spec` (R1): **was false in two cases** (R4's finding). Now R4's
  `changeV2_single` at the raft level: `applyChange (.v1 cc) m = (ConfChange.applyOne ⟨cc.type,
  cc.nodeId⟩ m).bind (fun m' => if m'.voters = ∅ then none else some m')` at a valid non-joint `m`.
  `ReqApplyOrRefuse`'s Assumes now says "with voters".
- `Membership.simple_valid.spec`: R4's premises (`W64 0 ∉ vs` only); `cluster_alloc.spec` drops its
  now-derivable `(Membership.simple …).Valid` premise.
- `persistent.spec` (R1), `logPersistent.spec` (R3): the raftpb conjuncts removed (raftpb's law).

## Sketches that did not fit, and the fixes

1. **R2's tracker was unreachable** (R2's `raftOpen` exposed the log and the read-only queue, not
   the tracker, yet `applyConfChange`, `switchToConfig`, `reset`, `poll`, the send helpers cite R4's
   tracker specs). And `switchToConfig`'s pre (`raftOpen ∗ trkResult`) could not be reached by
   `applyConfChange`: R4's `Changer` consumes the tracker's progress map, so `raftOpen` cannot be
   closed between the `Changer` and `switchToConfig`. Fixed in `ApiCore.lean`: `CoreOpen` gets the
   tracker's configuration (`conf`, so the invariant can state V1); new law `raftOpen_trk.spec` (the
   tracker out as R4's `progressTracker`, at `o.conf`/`o.view.prs`/`o.votes`, with `raftTrkOpen`
   closing at any tracker); `trkShell` (the struct, its votes and ring capacities, whose
   `Config`/`Progress` are about to be replaced). `raft.switchToConfig.spec` now takes
   `raftTrkOpen ∗ trkShell ∗ trkResult` and gives `o'.conf = m`. Its Users note how each caller
   reaches it (`newRaft` folds its struct into `raftOpen` first).
2. **`StableOk`/`SnapAckOk` take `handing = false`; `appliedLb` must be a floor** (R2 ↔ R3).
   `rawNodeAt_advance.spec`'s docstring now states its realization against R3's laws: the opening
   absorbs the written batch (`raftLog_absorb`: R1's `readyStor rn none j []` is R3's `logPending h
   false false`), so `handing = false` at the acknowledgements; the closing publishes the applied
   index (`raftLog_publish`, the frozen-term floor), which is R1's `appliedLb`.
3. **R1's storage laws against R3's `logStor_*`** (R1 ↔ R3): all derivable. R1's header now gives
   the precise mapping: `appliedLb n i` is `i = 0` or `logFloor l i t` with `t` the committed log's
   term at `i` (what `stor_createSnapshot`'s `s.term = t` needs, with `logFloor_agree`);
   `storSnapLb n j` is `j = 0` or `logSnapLb l j` (`zero_lbs`); `readyStor n so k es` is
   `logPending l h so.isSome (es ≠ [])`; the index-0 compaction and the empty append go through
   `logStor_read`. `isStorage`'s `Entries` already gives `len = cap`, `stor_read` already has
   `logStor_read`'s shape.
4. **`readOnly.maybeAdvance`** (R3 ↔ R4): its size premise restated in R4's form (`GMap.size … ≤
   Quorum.sortMax`), the `isAckedIndexer` instance named in its sketch.
5. **`raft.applyConfChange`'s premise** `∀ mm, applyChange (.v2 c2) mm = applyChange c mm`: now
   discharged by `applyChange`'s definition with 3h's `AsV2` specs (`c2 = c.asV2`); sketch updated.
6. **The sort bound** (R2 ↔ R4): R2's sketches of `bcastAppend`, `bcastHeartbeatWithCtx`, `reset`,
   `maybeCommit`, `poll` call R4's sorting specs, which take `GMap.size … ≤ 2^62`. Its intended
   source (the step bound, R4's question 2) is now written in `ApiCore.lean`'s realization item 5;
   it is the same open decision as the term bound (below).
7. **`logSliceFromMsgApp`** now gives the entries (`⌜m.type = MsgApp⌝ -∗ entriesRO ls.entries'
   (m.index + 1) m.entries`: raftpb's `msgPts_unfold` and `msgEnts_app`), as R3's `maybeAppend`
   takes them.
8. **The `MsgApp` entries' capacity: not fixable in the specs (a gap, recorded).** R3's
   `maybeAppend`/`append`/`truncateAndAppend` take the slice with `len = cap` or its capacity owned
   (Go's `truncateAndAppend` adopts it, `u.entries = ents`, and a later `append` writes into its
   capacity), and 3h decided `msgPts` grants no capacity (a `MsgApp` raft builds carries
   `limitSize`'s `ents[:limit]`, whose spare capacity is the leader's own log). Nothing in Go clips
   or copies the slice before the adoption, so `raft.handleAppendEntries` is not provable from the
   cited specs; its docstring records it. The fix is outside the specs, one of: (a) the fork clips in
   `logSliceFromMsgApp` (`slices.Clip(m.GetEntries())`: behavior-preserving, after which `len = cap`
   holds); (b) a received message's predicate owns its fresh capacity (2a's `Unmarshal`/`Clone`, a
   raftpb predicate for it, and every transport delivering a decoded or cloned copy: the old proof's
   `msgPtsC … cap`). A decision for the user. (Side note: in one process, a follower stepping a
   leader's `MsgApp` without a copy would adopt a slice whose capacity is the leader's unstable
   array; etcd always serializes, raft's own tests pass pointers. Not filed: no failing test.)
9. `confchange/Restore.lean`, `toConfChangeSingle.lean`, `tracker/ProgressTracker__ConfState.lean`,
   `pbEntryID.lean`, `assertConfStatesEquivalent.lean`: stale "provisional"/"requested" citations
   replaced by the real names.

## Requests

Addressed to my batches, now met:
- R2 → R1 item 8: `RawNode.HasReady`'s `false` case gives `⌜readyEmpty rd⌝`.
- R2 → R1 item 10: new law `bootLog_decided.spec` (each bootstrap entry's `confDecided … (.apply (.v1
  AddNode…))`, persistent, from `bootLog`).
- 2f → R1 (round 1): new law `msgSent_appShape.spec`; `readyGot` gives `∀ m ∈ b.msgs, m.type = MsgApp
  → m.src = id`.
- 2d → R1 (round 1) items 1 and 3: `BatchOk` bounds the committed entries' and the snapshot's terms
  by the batch's hard-state term; new law `msgSent_snapTerm.spec` (`MsgSnap` has a non-zero term).
- R4 → R1 items 1-3 (the model, the false law, `Valid`'s premises): done (above). Item 4 (ring
  bound): `ConfigOk` now has `sint.Z cv.MaxInflightMsgs' ≤ Tracker.inflightsMax`, marked in its
  docstring as R4's proposal and an open question (below).
- R4 → R2 item 6 (`progressCopyOwn`), R2's `trkResult` request: defined. R4 → R3: done.
- R1's request to 3h for `proto.Clone` of a `*Message`: met by composition (2a's `Clone.spec` with
  `RaftPb.msgPts_msgAt`: the clone holds the same content, so `msgPts p' (own 1) m`; `msgIs` gives
  depth `≤ 4`). The `msgPts` field-write laws (R2: `From`, `To` of an owned message): met by
  `RaftPb.msgPts_unfold` (`⊣⊢` at `own 1`: write the field's pointer, fold at the new model).
- 3h's `MarshalConfChange` size premise: `c.wireBound < Proto.marshalMax` added to
  `confChangeToMsg.spec`, `node.ProposeConfChange.spec`, `RawNode.ProposeConfChange.spec` (each
  docstring names 3h's open question 3 and the alternative).

Not done (with why):
- 2d → R1 (round 1) item 2, the stored entries' terms at most the stored hard state's at a start:
  false after a crash as R1 states crashes (`raftState_crash` keeps the old term with the batch's
  entries, which may be of a newer term). 2d must get the bound some other way (it is needed only for
  the merged-snapshot guard right after a restart, which `msgSent_snapTerm` and etcd's `raftTerm = 0`
  already exclude until the first hard state).
- R2 → R1 item 12 (`NewRawNode` restating `Config.defaulted`): no client needs it.
- R4 → R1 item 5 (`statusOwn_progress` over `progressValOwn`): etcd reads only the values; kept.

## The open decisions, stated consistently (not decided)

- **Term and index bound** (R1 Q9, R2 Q1): `cluster_alloc.spec`'s docstring now states it: an
  instance binder (R2's `∀ [ReceiptBoundLe GF (2^63)]`) at `2^63`, which also discharges R3's range
  premises and (item 6 above) R4's sort bound; not added to the statement. (R1's report said "below
  `2^64 - 1`"; R2's and R3's say `2^63`; `2^63` is what all the sketches need.)
- **`MaxInflightMsgs ≤ 2^62`** (R4 Q1): in `ConfigOk`, marked open.
- **`confAboveOk`** (R1 Q10): its docstring (`Model.lean`) and `raftState_crash.spec`'s now say it
  guards a real raft bug (`issues/raft-commit-lost-with-entries-kept.md`, reproduced), and that
  whether etcd takes it as a scope restriction is the user's question.
- **`MarshalConfChange`'s size premise** (3h Q3): as above.
- **`MsgApp` capacity**: item 8 above (new).

## What I need from directories I don't own

Nothing for the build. For provability, outside the specs: item 8's choice (the fork's
`logSliceFromMsgApp`, or 2a's `Unmarshal`/`Clone` granting fresh capacity of repeated fields, with
2f's decoders and `examples/`' in-process transports delivering such copies).

## Files changed

`Spec/go_etcd_io/raft/v3/`: `Model.lean`, `Api.lean`, `ApiCore.lean`, `ApiLog.lean`,
`RawNode__HasReady.lean`, `RawNode__Ready.lean` (an unused binder), `RawNode__ProposeConfChange.lean`,
`node__ProposeConfChange.lean`, `confChangeToMsg.lean`, `raft__switchToConfig.lean`,
`raft__applyConfChange.lean`, `raft__handleAppendEntries.lean`, `logSliceFromMsgApp.lean`,
`readOnly__maybeAdvance.lean`, `pbEntryID.lean`, `assertConfStatesEquivalent.lean`;
`confchange/{Model,Api,Restore,toConfChangeSingle}.lean`; `tracker/ProgressTracker__ConfState.lean`.
`examples/specreq/raftnode/confchange.go` (an Assumes line).
