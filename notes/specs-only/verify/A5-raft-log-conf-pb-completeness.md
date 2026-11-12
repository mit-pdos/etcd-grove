# A5 (raft log / tracker-quorum-confchange / raftpb): completeness

Reviewer: verification round, kind **completeness**, 2026-11-09, at `1aa6fc1337`. I wrote these
findings before reading the batch reports and open-questions. I read those afterwards only to mark
which findings are already recorded.

## Verdicts

| batch | verdict |
|---|---|
| R3 (raft log, unstable, readOnly, util: `ApiLog.lean` and its specs) | **PASS WITH OPEN DECISIONS**: the `lastIndex < 2^63` / sort bounds come from R1's `cluster_alloc` receipts, which is an open user decision (`ApiCore.lean:110-121`) |
| R4 (tracker, quorum, confchange) | **FAIL** (F2) |
| 3h (raftpb) | **FAIL** (F1, F3, F4, F5) |

Counts:
- Specs checked for coverage: 484 `.spec` definitions in the area. Against `specs-ref`, four are missing: 2 in the area, 2 just outside it (below).
- Snippets checked against users: 50 (raftlog 18, raftconf 18, raftpb 14). 49 close. `raftpb/ReqBootstrapBytes` does not (F3).
- User patterns checked: 14. 10 close.
- Callers' specs checked for fit: 16. 11 fit.

## First-tier findings

**F1 (3h, coverage). `MessageType.String` lost its spec, and rafthttp's verified code calls it.**
- **What changed.** `specs-ref` had `raftpb/MessageType__String.lean` and `ConfChangeType__String.lean`. Here both are "left out (untranslated, logging only)" (`batch-3h.md`, "Left out").
- **Why it matters.** `String` is untranslated (`Code/go_etcd_io/raft/v3/raftpb.toml`: `"!*.String"`), but rafthttp's translated bodies call `raftpb.MessageType.String` 7 times on reachable paths:
  - `transport.go:205`: `Transport.Send`, unknown peer;
  - `peer.go:256`: the send buffer is full;
  - `remote.go:78,89`;
  - `http.go:256`;
  - `stream.go:537,548`.
- **Effect.** The proof sketches of 2f's `Transport.Send`, `peer.send`, `remote.send`, the stream reader and `pipelineHandler` have no callee spec for these calls; `Transport__Send.lean`'s sketch says only "dropped, logged". Translated code calling into an untranslated method needs an assumed spec whether or not the result is only logged.
- **Fix.** Restore `raftpb.MessageType.String.spec` as a trust-boundary spec ("returns some string": the old `fmt.stringMethodSpec` form, restated over this branch's conventions).
- **Lower priority.** `ConfChangeType.String` and `EntryType.String` are reached only on `lg.Panic` paths: `membership/cluster.go:386`, `storage/util.go:128`, `server.go:1961`.

**F2 (R4, with R1 and 2d as users). `ProgressTracker.ConfState` gives `confStatePts` where Go builds a full `ConfState`, so etcd's snapshot paths cannot be served.**
- **What Go does.** `tracker.go:148-155` sets `AutoLeave: new(p.AutoLeave)`: the result is always full.
- **What the spec says.** `tracker/ProgressTracker__ConfState.lean` returns `RaftPb.confStatePts csp (own 1) …`, which drops fullness. R1's `node.ApplyConfChange` and `raftNode.ApplyConfChange` inherit `confStatePts` (`raftNode__ApplyConfChange.lean:49`). No spec outside raftpb mentions `confStateFull`.
- **Users not served:**
  - **(a) `createMergedSnapshotMessage`** (`snapshot_merge.go:43-50`). It builds `&Snapshot{Metadata: &SnapshotMetadata{…, ConfState: proto.Clone(confState)}}` and stores it in `m.Snapshot`. The new message needs `msgPts`, which requires a full snapshot (`msgFields`: `snapshotPts`, then `snapMetaGo … true`, then `confStateFull`): `snap.NewMessage.spec` takes `Raft.msgPts`. The server holds only `confStatePts cs □ csm` (`EtcdServer__createMergedSnapshotMessage.lean:60`). A clone of that is `confStatePts` again (`confStatePts_msgAt` with `full = false`), so the step to `NewMessage` does not close.
  - **(b) `MemoryStorage.CreateSnapshot(ep.appliedi, ep.confState, nil)`** (`server.go:2132`). R1's spec (`MemoryStorage__CreateSnapshot.lean`) takes `confStatePts csp dq cs` and promises `snapshotPts sp … (σ.createSnapshot …).snap`. Go stores `proto.Clone(cs)` (`storage.go:258-262`), which is not full when `cs.AutoLeave` is nil. So that spec is **false** at a non-full input: a soundness defect of R1's spec, and it has the same root.
- **Fix.**
  1. `ProgressTracker.ConfState.spec` returns `confStateFull`.
  2. `raft.switchToConfig`, `applyConfChange`, `node`/`RawNode.ApplyConfChange` and etcd's `raftNode.ApplyConfChange` pass it through.
  3. `MemoryStorage.CreateSnapshot.spec` takes `confStateFull`.
  4. The server keeps `ep.confState` as `confStateFull`. Its sources are all full: ApplyConfChange, and a `Ready` or stored snapshot's metadata through `snapMetaGo … true`.
- **Recorded?** Not recorded.

**F3 (3h). Bootstrap determinism is still unconnected, although 2a now provides it.**
- **The gap.** R1's `BootLog` (`Model.lean:412-417`) fixes each bootstrap entry's data as `bootEntryData id ctx`, an opaque byte string (`raftpb/Model.lean:424`). `RawNode.Bootstrap`'s proof gets the bytes from `proto.Marshal`, whose post is `encodes t c bs ∧ (noMaps t → bs = marshalOut t c)` (`proto/Marshal.lean:51`). But:
  - no law gives `Proto.noMaps raftpb.ConfChange.ty`: the only other mention of `noMaps` is `pbutil/MustMarshalMessage.lean`;
  - no law ties `bootEntryData id ctx` to `marshalOut ConfChange.ty c` for the `c` with `bootCC id ctx c`;
  - `bootCC_facts` gives only `encodes c (bootEntryData id ctx)`, and encodings are not unique.
- **Effect.** Bootstrap's post (entries equal to `BootLog`'s bytes, the same at every founder) does not close. The snippet `raftpb/snapshot.go:ReqBootstrapBytes` is still marked "BLOCKED on 2a's marshalOut"; that note is stale, since 2a has it (`proto/Api.lean:116-126`).
- **Fix (in raftpb's laws).** Either add `noMaps_raftpb.spec` (every raftpb message type has no map field) and `bootEntryData_out.spec : bootCC id ctx c → bootEntryData id ctx = Proto.marshalOut raftpb.ConfChange.ty c`, or define `bootEntryData` as that `marshalOut`. Then update the snippet's header.
- **Recorded?** Recorded as `batch-3h.md` open question 5 ("until 2a states it"). 2a has since stated it, and the gap was not closed.

**F4 (3h, with R1 and 2f as users). `msgRecv` has no introduction law, so no real caller of `node.Step` can establish its precondition.**
- **The requirement.** `node.Step.spec` (`node__Step.lean:58`) and `RawNode.Step.spec` require `msgRecv ml m` for every message, not only `MsgApp`. raftpb gives `msgRecv` only through `msgRecv_unfold`: the fields plus `ownSliceCap` of `Entries`.
- **Why no one can supply it.** Protobuf's `Unmarshal.spec` and `Clone.spec` (`proto/Unmarshal.lean`, `Clone.lean`) give `msgAt … (own 1) c` (and `decodedAt`), never the capacity of repeated fields. No law turns a decoded or cloned `msgAt raftpb.Message.ty` into `msgRecv`.
- **What the callers hold** is `msgPts (own 1)`, not `msgRecv`:
  - rafthttp's decoders (`messageDecoder__decodeLimit.lean`, `msgAppV2Decoder__decode.lean`) deliver `msgPts ml (own 1) m`;
  - rafthttp's `Process` contract (`rafthttp/Api.lean:263`), `EtcdServer.Process` (`EtcdServer__Process.lean:53`) and etcd's `raftNode.Step` (`raftNode__Step.lean:34`) take `msgPts`;
  - the in-process transport snippet (`raftnode/transport.go:19`) relies on `proto.Clone` giving `msgRecv`.
- **Effect.** `raftNode.Step`'s sketch ("R1's `node.Step.spec`") does not close, and every network path into raft is cut.
- **Recorded?** Coordinator decision A12 (`open-questions.md:67`) chose `msgRecv` and said "rafthttp's decoders and `Unmarshal`/`Clone` supply it". That supply was never written: the decision is recorded but not carried through.
- **Fix.**
  1. 2a's `Unmarshal`/`Clone` posts give a fresh-capacity fact for repeated fields (e.g. a persistent `Proto.freshSlices t p`, or `decodedAt` extended).
  2. raftpb adds `msgRecv_intro.spec : msgPts p (own 1) m ∗ <that fact> ⊢ msgRecv p m`.
  3. The decoders, `Process` and `raftNode.Step` carry `msgRecv`.

  Or take A12's alternative (clip in `logSliceFromMsgApp`) and go back to `msgPts`.

**F5 (3h, with R1 as user). `msgPts` cannot describe a message with `Responses`, so two R1 specs promise something false.**
- **The restriction.** `msgFields` fixes `Responses` to `rs ↦*□ []` (`raftpb/Api.lean`, last conjunct of `msgFields`).
- **The false posts.**
  - `newStorageApplyMsg` always sets `Responses: []*pb.Message{newStorageApplyRespMsg(…)}` (`rawnode.go:380`).
  - `newStorageAppendMsg` sets `Responses = r.msgsAfterAppend`, plus the append acknowledgement when `needStorageAppendRespMsg` holds (`rawnode.go:254-258`).

  Yet `newStorageApplyMsg.spec` and `newStorageAppendMsg.spec` both return `msgPts p (own 1) mm`. That is false for `newStorageApplyMsg` at every call, and for `newStorageAppendMsg` whenever a response is attached. Their preconditions (`raftOpen …`) do not exclude the call. That the branch is "unreachable under `ConfigOk`" is a reason a caller does not reach them, not a reason the triples hold.
- **Fix.** Either weaken the two posts to what raftpb can state (e.g. `msgAt raftpb.Message.ty p (own 1) c` with only the stated fields), or add a raftpb predicate for a message with responses. Alternatively, mark these two internal helpers as having no spec (`ConfigOk` excludes async writes), recorded as a scope restriction.
- **Recorded?** Not recorded.

## Second tier

- **Coverage outside A5.** `specs-ref` had `MemoryStorage__firstIndex.lean` and `MemoryStorage__lastIndex.lean` (unexported helpers in `storage.go`, R1's area). They have no spec here; R1's `FirstIndex`/`LastIndex` sketches presumably inline them, so they should be marked as left out.
- **Quorum's sort bound.** `Quorum.sortMax` is described as "kept local to the two `CommittedIndex` specs" (`quorum/Api.lean:46-49`), yet it is a premise of `Visit`, `ConfState`, `LearnerNodes`, `VoterNodes`, `QuorumActive` and `readOnly.maybeAdvance`. Callers discharge it from the open `receiptBound` decision (`ApiCore.lean:114-121`). The header should say so.
- **The log's laws are reached only through prose.** R3's storage-write and absorb laws (`logStor_*`, `raftLog_absorb`, `raftLog_publish`, `logFresh_attach`, `raftLog_borrowStarting`, `raftLog_storageLastIndex`) are cited by no spec outside `ApiLog.lean`. They are reached through R1's `Api.lean:74-84` and R2's `rawNodeAt_advance` docstring (`ApiCore.lean:507-514`). The fit checks out in that prose (`readyStor … = logPending h false false`, `appliedLb = ∃ t, logFloor`), but no machine-checkable citation ties them.

## What is good

- `ApiLog.lean`'s `LogState` is Go-shaped, so the read specs are "returns what Go computes". The compaction margin is one `compactFloor` disjunct with a persistent `logCompactedLb` that `raftLog.snapshot` consumes. `maybeAppend`'s premises are exactly what `handleAppendEntries` establishes (the `prev < committed` early return, log matching).
- confchange's model (`changeV2`, `restore`, `applyOne`) mirrors `confchange.go` step by step, including:
  - node `0` skipped, which is etcd's refused change (`server.go:2041`, `cc.NodeId = new(raft.None)`);
  - the "removed all voters" check;
  - `Simple`'s path that returns `tracker.Config{}, nil, err` (not `c.err`).

  `changeV2_single` matches `applyChange_v1` as etcd uses it.
- The raftpb unfold and relation laws serve every etcd raftpb pattern except F2 and F4:
  - getters through `nil`;
  - composite literals plus `pbRest_zero`;
  - field writes with fresh cells (`cc.Id = new(…)`, `cc.NodeId = new(raft.None)`);
  - `pbutil.MustUnmarshalMessage(&cc, e.Data)` to `confChangeV1Pts` via `encodes_fun` and `decodeConfChange`'s definition;
  - wire round trips.
- etcd's `isLearnerReady` (`server.go:1585-1630`) reads `rs.Progress[...]` values only: served by R1's `statusOwn_progress` (no tracker spec needed). It needs no fact about `Match`.

## Users checked

| pattern | site | snippet | closes |
|---|---|---|---|
| getters, incl. through `nil` | `server.go:1935-1965`, `storage/util.go:103-107`, rafthttp | `raftpb/messages.go` ReqGettersNil | yes |
| build a `ConfChange` and propose it | `server.go:1422,1475,1552,1685,1781` | `raftpb/confchange.go` ReqMarshalDecode | yes |
| decode a committed conf entry | `server.go:1948-1950` | ReqMarshalDecode | yes |
| refused change: `NodeId := 0`, `ApplyConfChange` | `server.go:2041-2042` | `raftconf` ReqApplyLikeRaft, `changeV2_single` | yes |
| `ConfState` from `ApplyConfChange` to `SetConfState` | `server.go:2053-2055` | none in A5 | yes (`confStatePts` suffices there) |
| `ConfState` to `CreateSnapshot` / merged snapshot | `server.go:2132`, `snapshot_merge.go:43-50` | none | **no (F2)** |
| `IsEmptySnap` / `IsEmptyHardState` / `MustSync` | `raft.go:222-272`, `server.go:1022`, `wal.go:1023-1047` | `raftlog/util.go` | yes |
| message encode / decode on the wire | rafthttp `msg_codec.go`, `msgappv2_codec.go`, `http.go` | ReqWireRoundTrip | yes for `msgPts`; **no for `Step` (F4)** |
| enum `String()` in logs | rafthttp (7 sites) | none | **no (F1)** |
| received message stepped into raft | `server.go:721` (`Process`), examples' transport | `raftnode/transport.go` ReqDeliver | **no (F4)** |
| bootstrap entries | `bootstrap.go:52-56` via `StartNode` | ReqBootstrapBytes | **no (F3)** |
| `Status.Progress` | `server.go:1590-1615` | `raftconf/voters.go` ReqProgressCopy | yes |
| confchange pre-check | `examples/raft/kvreconf/kv.go:219`, `kvdurable/kv.go:228-252` | ReqApplyLikeRaft | yes |
| log, unstable, readOnly (raft-internal) | `raft.go` / `rawnode.go` via R2's sketches | `raftlog/*` | yes (with the open bound decision) |

## Bug check

No Go bug found. F2's falsity is in R1's `MemoryStorage.CreateSnapshot.spec`, not in Go: etcd always passes a full `ConfState`.
