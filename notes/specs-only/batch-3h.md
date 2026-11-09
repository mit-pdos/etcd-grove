# Batch 3h: the protobuf message packages (raftpb, etcdserverpb, mvccpb, version)

Author's report (round 0). Every file builds (`etc/specs-build.sh --dir` of the three directories:
58 + 85 + 2 modules). Snippets vet clean (`go vet ./specreq/raftpb/ ./specreq/etcdserverpb/`).

## Files

- `Spec/go_etcd_io/raft/v3/raftpb/`: `Model.lean` (pure: R1's message models field for field, the
  enumerations, `ConfChangeV2.enterJoint`/`leaveJoint`, `ConfChangeI.asV2`, the content readers, the
  `*Is` relations, `decodeConfChange`, `msgEncodes`, `entryEncodes`, `bootCC`, `bootEntryData`, the
  size bounds), `Api.lean` (resources and laws), and 56 function specs: 40 getters, 4 `Enum`,
  `MarshalConfChange`, `ConfChange.AsV2`/`AsV1`, `ConfChangeV2.AsV2`/`AsV1`/`EnterJoint`/
  `LeaveJoint`, `ConfChangesToString`, `ConfState.Equivalent`, `EnsureConfState`,
  `EnsureSnapshotMetadata`, `EnsureSnapshot`.
- `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/`: `Api.lean` (the content relations, 2a's slots, the
  descriptors' and enum maps' init laws, the WP shapes of stubs and handlers; no client vocabulary),
  `Realize.lean` (the laws over 1b's and 1c's predicates), and 83 function specs: 39 getters,
  `New{KV,Watch,Lease,Auth}Client` (client-facing: `connOk ⊢ remote*At`), 17 stub methods
  (`kVClient.*`, `leaseClient.*`, `authClient.*`, `watchClient.Watch`), 17 handlers (`_KV_*`,
  `_Lease_*`, `_Auth_*`, `_Watch_Watch`), 6 `Register*Server`.
- `Spec/go_etcd_io/etcd/api/v3/version/`: `Cluster`, `LessThan` (assumed: names-only translation).
- `examples/specreq/raftpb/`: `messages.go`, `confchange.go`, `snapshot.go` (14 snippets).
- `examples/specreq/etcdserverpb/`: `getters.go`, `stubs.go` (8 snippets).

Namespaces: `RaftPb` (new), `EtcdServerPb` (new), `Version` (new).

## The design (one paragraph)

A message's ownership predicate is opaque, with two kinds of laws: a **field-level unfold law**
(what the Go code reads and writes) and a **relation law to protobuf's `Proto.msgAt`** (2a), `xPts
p dq m ⊣⊢ ∃ c, Proto.msgAt T.ty p dq c ∗ ⌜xIs c m⌝`, where `c : Proto.Content` is a value and `xIs`
is a pure relation, functional in the content. Clone, Marshal, Unmarshal, Size, Equal and Merge are
2a's specs over `msgAt`; the relation laws carry a model across them, and over gRPC (a server's
decoded request holds the client's content). No law relates two addresses or two heaps; no
statement quantifies over a caller-built wire model (the old `pbEnc`/`PbType`/`ProtoMsg` bugs:
`specs-ref/notes/{pbenc-ok-inconsistent,per-type-blockers,grpc-msg-models}.md`). Decoding is a
function because `Proto.encodes` is (`encodes_fun`), so `decodeConfChange` is a definition, not an
opaque.

## Exported vocabulary

### raftpb (`RaftPb`)

Pure (`Model.lean`): `LogEntry`, `HardState`, `ConfState` (+ `Equiv`, `lenOk`, `wireBound`),
`SnapMeta`, `Snapshot` (+ `meta`, `wireBound`), `ConfChangeV1`/`ConfChangeSingle`/`ConfChangeV2`/
`ConfChangeI` (+ `asV2`, `entryType`, `enterJoint`, `leaveJoint`, `wireBound`), `Msg` (+
`entryIndexes`: a `MsgApp`'s entries at `index + 1, ...`; `wireBound`); content readers (opaque
functions) `entryIndexOf`, `entryOf`, `hardStateOf`, `confStateOf`, `csFull`, `snapMetaOf`,
`snapshotOf`, `snapFull`, `msgOf`, `msgEntryIndexes`, `msgSnapFull`, `msgNoResponses`,
`confChangeOf`, `confChangeV2Of`, `singleOf`, `plain` (no unknown fields); `msgWf`; the relations
`entryIs`, `hardStateIs`, `confStateIs c cs full`, `snapshotIs c s full`, `msgIs`, `confChangeV1Is`,
`confChangeV2Is`, `singleIs` (each: the readers, plainness, `Proto.marshalOk`, a depth bound, an
encoded-size bound by the model); `decodeConfChange` (definition), `msgEncodes`, `entryEncodes`;
`bootCC id ctx c` (opaque relation), `bootEntryData` (opaque bytes).

Resources (`Api.lean`, opaque): `entryPts p dq i e`, `hardStatePts`, `confStatePts` (any presence),
`confStateFull` (`AutoLeave` set), `snapshotPts` (full: `Ensure*` writes nothing), `snapshotRaw` (any
presence), `msgPts` (well-formed), `confChangeV1Pts`, `confChangeV2Pts`, `singlePts`, `pbRest`.
Definitions: `optCell`, `entryRO`, `entriesRO`, `entryPtrs`, `msgEnts`, `confChangePts`, `ccsPts`,
`confStateGo`, `snapMetaGo`, `snapshotGo`.

What `dq` covers: the message struct's fields at `dq`; every pointee raft shares read-only for good
(scalar cells: `&pb.Message{To: m.From}` shares the request's cell; byte slices; a message's entries
and snapshot); at `dq` only what Go writes in place (a snapshot's metadata and conf state, a
`ConfState`'s lists, a `ConfChangeV2`'s changes).

Laws: `raftpb_persistent`, `raftpb_timeless`, `raftpb_ne_null`, `raftpb_persist` (persist; two
holdings agree), `pbRest_zero`, unfold laws (`entryPts_unfold`, `hardStatePts_unfold`,
`confStatePts_unfold`, `confStateFull_unfold`, `snapshotPts_unfold`, `snapshotRaw_unfold`,
`msgPts_unfold`, `confChangeV1Pts_unfold`, `confChangeV2Pts_unfold`, `singlePts_unfold`), relation
laws (`*_msgAt`, one per predicate), `msgEnts_app` (a `MsgApp`'s entries are `entriesRO sl (index +
1)`), `confState_ext` (a plain full conf-state content is its model), `bootCC_lit` (the bootstrap
literal holds the bootstrap content), `bootCC_facts` (unique, its model, `encodes … (bootEntryData
id ctx)`), `decodeConfChange_empty`, `wire_fun` (`msgEncodes`, `entryEncodes` functional).

### etcdserverpb (`EtcdServerPb`)

`Api.lean`: relations (opaque, functional) `reqHolds c rq`, `bodyHolds c b`, `respHeaderHolds`,
`keyValueHolds`, `rangeRespHolds`, `putRespHolds`, `deleteRespHolds`, `responseOpHolds`,
`txnRespHolds`, `compactRespHolds`, `compareHolds`, `requestOpHolds`, `chunkHolds`; `reqType`,
`bodyType`; **2a's slots realized**: `reqModels`, `replyModels`, `chunkModels`; `mergeW`,
`mergeHeader`, `mergeRange` (protobuf's merge of range replies). Laws: `holds_fun`, `holds_depth`,
`rangeResp_merge`, relation laws for W0's 15 predicates (`rangeReqOwn_msgAt`, ...,
`compactRespOwn_msgAt`), the init laws `kvDesc_init`, `watchDesc_init`, `leaseDesc_init`,
`authDesc_init`, `otherDescs_init` (grpc's `serviceDescAt` of each descriptor), `descStreams_init`,
`sortNames_init`. Shapes: `stubAt`, `unaryStubWP`, `streamStubWP`, `handlerBodyWP`, `embedTestTy`.

`Realize.lean`: `watchReqHolds`, `watchRespHolds`, `eventHolds` (+ `watch_holds_fun`,
`watch_holds_depth`); `watchReqOwn_msgAt`, `wireWatchRespOwn_msgAt`, `eventOwn_msgAt`,
`reqOwn_msgAt`, `replyOwn_msgAt`, `replyOwn_lease` (the lease replies' fields the lessor copies),
`userAddOptsAt_unfold`, `statusRespOwn_msgAt`. 2b's offered laws (`watchReqOwn_unfold`,
`wireWatchRespOwn_unfold`, `wireWatchRespOwn_persist`) are accepted as this batch's obligations.

## What replaces each provisional name (for integration)

| provisional | where | replaced by |
|---|---|---|
| `entriesRO sl k es` | R1 `Api.lean` | `RaftPb.entriesRO` (same signature, now a definition) |
| `msgPts p dq m` | R1 | `RaftPb.msgPts` |
| `hardStatePts p dq hs` | R1 | `RaftPb.hardStatePts` |
| `snapshotPts p dq s` | R1 | `RaftPb.snapshotPts` (full; `snapshotRaw` for any presence) |
| `confStatePts p dq cs` | R1, R4 | `RaftPb.confStatePts` (any presence; `confStateFull` when ensured) |
| `confChangePts v dq c` | R1, R2 | `RaftPb.confChangePts` (definition over `confChangeV1Pts`/`V2Pts`) |
| `entryRO p k e` | R3 `ApiLog.lean`, 2d `ApiApply.lean` | `RaftPb.entryRO` (definition: `entryPts p □ (W64 k) e`) |
| `entryPtrs sl dq es` | R2 `ApiCore.lean` | `RaftPb.entryPtrs` |
| `ccsPts sl dq cs` | R4 `confchange/Api.lean` | `RaftPb.ccsPts`, over `RaftPb.ConfChangeSingle` (= R4's `ConfChange.Single`: same fields) |
| `decodeConfChange` (opaque) | R1 `Model.lean` | `RaftPb.decodeConfChange` (definition) |
| `bootEntryData` (opaque), `bootEntryData_decode` | R1 | `RaftPb.bootEntryData`; the law follows from `bootCC_facts` and `decodeConfChange`'s definition |
| R1's `LogEntry`, `HardState`, `ConfState`, `Snapshot`, `ConfChange*`, `Msg`, enums | R1 `Model.lean` | `abbrev X := RaftPb.X` (same field names; R1's `Model.lean` imports `raftpb/Model.lean`, which imports nothing of raft's) |
| `ConfState.Equiv` | R3 `ApiLog.lean` | `RaftPb.ConfState.Equiv` (same definition) |
| `pbEncodes e m` | 2f `rafthttp/Api.lean` | `RaftPb.msgEncodes e m` (functional: `wire_fun`) |
| `reqModels`, `replyModels`, `chunkModels` | 2a `v3rpc/Api.lean` | `EtcdServerPb.reqModels`, `replyModels`, `chunkModels` |
| `irrOwn`, `alarmReqOwn`, `irrIsRevoke` | 2c `ApiReq.lean`, `ApiBoot.lean` | **not yet**: see open question 4 |

## Main changes from the old specs

- **The wire model is content-keyed** (above). The old `pbEnc ty l` (keyed by address) and the
  caller-built `PbType`/`ProtoMsg` are gone; `MarshalsConfChange`, `EqualConfState` and the per-type
  proto specs are replaced by 2a's generic specs plus this batch's relation laws.
- **Presence.** The old `ownSnapE`/`W`/`S` hierarchy (successive strengthenings of "which pointer
  fields are set") is two predicates: any presence (`snapshotRaw`, `confStatePts`) and full
  (`snapshotPts`, `confStateFull`), which is what `Ensure*` distinguishes (writes or not).
- **`Message.GetEntries`** no longer lends the slice's capacity: a `MsgApp`'s `Entries` is a sub-slice
  of the leader's log (`raftLog.entries`), so a message cannot own its capacity. R3 asked for it
  (`maybeAppend` adopting the slice); see open question 2.
- **`ConfState.Equivalent`**: both outcomes specified (`nil ↔ Equiv`); the sort bound is in the
  predicate (`ConfState.lenOk`, which R4's valid configurations meet).
- **`MarshalConfChange`**: an explicit size premise (`c.wireBound < 2 ^ 48`); the old spec had none
  because the old proto boundary had none (false of protobuf-go); `nil` is the same spec.
- **Stubs and handlers**: WP forms over grpc's contents (`attemptOk`/`Invoke`, `decOk`), composed by
  2a (`icChain_call`, `regsOk`), instead of the old `grpcHandlerOkMd`/`ProtoMsg` statements; the
  client-facing statement is the constructor's (`NewKVClient: connOk ⊢ remoteKVAt`).
- `version.Cluster`: the post (`semverStr → asciiStr`) dropped (only logged).

## Left out

- `ConfChangesFromString` (only `rafttest` calls it), `MessageType.String`, `ConfChangeType.String`
  (untranslated: `!*.String`), `AlarmType.String`, `RangeRequest.String`, `NewLoggableTxnRequest`
  (untranslated, logging only).
- The other getters of etcdserverpb's translated messages that no spec or snippet reads.
- `authpb`'s getters (`User.GetName`, ...): no request; the auth store's batch (3d) will need the
  `User`/`Role`/`Permission` predicates (its own model): to be added on request.
- `mvccpb.Event.IsCreate`/`IsModify` (1b asked): untranslated (the toml translates `KeyValue`,
  `Event` and the two constants only). Kubernetes reads them; see open question 1.

## Open questions for the user (and the coordinator)

1. **Translation gaps** (`Code/go_etcd_io/etcd/api/v3/{etcdserverpb,mvccpb}.toml`, not this
   batch's to change): 1c asked for `Member`, `MemberAddResponse`, `MemberListResponse`,
   `StatusResponse` (and `AlarmResponse`'s fields) translated as structs; W0's `sortNames_init`
   needs `RangeRequest_SortOrder_name`/`_SortTarget_name` translated; 1b's `Event.IsCreate`/
   `IsModify`; the Cluster and Maintenance handlers (`_Cluster_*_Handler`, `_Maintenance_*`), the
   `RangeStream` stub and handler, and `NewClusterClient`/`NewMaintenanceClient` are names only, so
   a member's Cluster/Maintenance services and the client's `RangeStream` have no generated code to
   verify. The laws that mention them are stated (`replyOwn_msgAt` covers their contents) but some
   cannot be proved until the translation includes them.
2. **R3's capacity request** (`maybeAppend` adopting a `MsgApp`'s slice): not given. raft's own
   `MsgApp`s carry a sub-slice of the leader's log; a message cannot own its capacity. R3/R2 must
   not let `unstable` append into an adopted slice without owning its capacity (R2's
   `logSliceFromMsgApp` could clip it, or R3 copy on append): a question for R2/R3 at integration.
3. **`MarshalConfChange`'s size premise** (`c.wireBound < 2 ^ 48`, a context under ~2^47 bytes):
   R1's `ProposeConfChange.spec` must carry it (a client-facing premise; true of every real change,
   but stated). Alternatively a workload premise like grpc's `msgsFit`. The user's choice.
4. **The `InternalRaftRequest`** (2c's provisional `irrOwn`, `alarmReqOwn`, `irrIsRevoke`): its
   model `IrrBody` is 2c's (`ApiReq.lean`), above this package. Realizing it here needs either the
   model moved down into `etcdserverpb` (it is the raft request's content: a field per request kind)
   or the relation law `irrOwn_msgAt` stated in 2c's file over a relation 3h would add
   (`irrHolds c ir`). Proposed: move `IrrBody` down at integration; 3h then adds `irrHolds` and its
   laws in the same shape as `reqHolds`.
5. **Bootstrap determinism** is a fact of protobuf-go that 2a's boundary does not state yet
   (`req/google_golang_org_protobuf_proto.md`, "from 3h", item 1); until then `bootEntryData` is
   opaque with `bootCC_facts` (it encodes the bootstrap content), which does not give R1 equal bytes
   at two founders.

## `req/` sections written

- `req/google_golang_org_protobuf_proto.md`, "from 3h": `Marshal` deterministic (`marshalOut`), the
  empty bytes decode to the zero message, one shared bookkeeping predicate.
- `req/google_golang_org_grpc.md`, "from 3h": `grpc.StaticMethod()`, interface dispatch of the
  connection interface, `HandlerTriple`'s home.
