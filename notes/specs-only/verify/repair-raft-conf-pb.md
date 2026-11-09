# Repair: group `raft-conf-pb` (tracker, quorum, confchange, raftpb)

Repair round after the verification round (2026-11-09), per `notes/specs-only/repair-brief.md`.
Files owned: `Spec/go_etcd_io/raft/v3/{tracker,quorum,confchange,raftpb}/`,
`examples/specreq/{raftconf,raftpb}/`. Reports worked from: `A5-raft-log-conf-pb-provability.md`
(R4 and 3h parts), `A5-raft-log-conf-pb-completeness.md` (R4 and 3h parts), and
`A4-raft-node-core-completeness.md` (no finding there is about R4's files; its F1 to F5 are R1's).

## Findings

### A5-provability

- **F1 (3h part: `ConfChangesToString`)**: fixed. It is now stated as **assumed** (trust
  boundary): the body is translated, but it uses `strings.Builder` methods and `fmt.Fprintf`, which
  have no spec in Perennial or here. The block comment says why the triple is true of Go. The
  `Users` line is corrected: `util.go:216` is `DescribeEntry`, which has no spec, so the function has
  no specified caller. File: `raftpb/ConfChangesToString.lean`. The R3 part (`DescribeConfChange`)
  is raft-core's file: see the requests.
- **F2 (`Changer.apply`'s "unexpected conf type")**: fixed with a raftpb-local assumed boundary
  spec, `RaftPb.fmtErrorf.spec` (`raftpb/FmtErrorf.lean`). It is Perennial's `fmt.Errorf.spec`
  (a non-nil error whose `Error()` returns some string) with a wider argument rule: besides
  Perennial's `ArgWf`, it accepts a raftpb enum value (`FmtArg.enum`) and a `*ConfState` the caller
  holds (`FmtArg.confState`, given back). It holds for every verb, as the header argues from
  `fmt/print.go` and protoc-gen-go's `String` methods.
  - `Changer.apply`'s block comment now has a Proof sketch that cites it, and a `Changes:
    verify-round` line. File: `confchange/Changer__apply.lean`.
  - **Fixed differently**: the old tree's general `Spec/fmt/Errorf.lean` (`argsOk`,
    `stringMethodSpec`) was not restored, because `Spec/fmt/` is client-core's. The local spec does
    not need `ConfChangeType.String`'s spec either: under `%d` Go calls no method.
- **F3 (`ConfState.Equivalent`'s mismatch branch)**: fixed by the same `fmtErrorf.spec`, with four
  `FmtArg.confState` arguments (the two clones at `own 1`, the inputs at their fractions). This
  keeps the stronger two-sided spec. The sketch and Changes are updated. File:
  `raftpb/ConfState__Equivalent.lean`.
- **F4 (`bootEntryData` vs `proto.Marshal`)**: fixed by two new laws in `raftpb/Api.lean`:
  - `noMaps_raftpb.spec`: `Proto.noMaps` for all nine raftpb message types;
  - `bootEntryData_marshal.spec`: `bootCC id ctx c → bootEntryData id ctx = Proto.marshalOut
    raftpb.ConfChange.ty c`, under the name raft-core cites. Its intended realization is stated:
    `bootEntryData` is defined as that `marshalOut`.

  The `Model.lean` header is updated. The snippet `raftpb/ReqBootstrapBytes` is unblocked: its
  `BLOCKED` note is gone, and it now cites `Marshal.spec` and the two laws.
- **F7 (`proto.Uint64` in `raftconf` snippets)**: fixed. `single` uses `new(id)` and the `proto`
  import is gone. `ReqLastVoter`, `ReqJointCycle` and `ReqLearnerFlag` use `single`. File:
  `examples/specreq/raftconf/confchange.go`.
- **F8 (`ReqLearnerFlag` reads `trk.Learners`)**: fixed as the reviewer suggested.
  - It now reads the learners through `trk.LearnerNodes()` (`ProgressTracker.LearnerNodes.spec`,
    with the snippet's existing 2^62 assumption) and a local loop `contains`. It does not use
    `slices.Contains`, because Perennial has no spec of it.
  - `configOwn_open` is not widened: raft never reads `Learners`/`LearnersNext` directly.
  - File: `examples/specreq/raftconf/voters.go`.
- **S4 (`ReqCloneFresh` deletes from the map it ranges over)**: fixed cheaply. The loop now ranges
  over `c.Voters.IDs()`, a fresh map by `JointConfig.IDs.spec`, and deletes from `c.Voters[0]`.
  File: `examples/specreq/raftconf/tracker.go`.
- **S5 (header names `mergeDstOk`)**: the header already says `Proto.mergeDst` "replaced 3h's
  `mergeDstOk`" (history, not a use). The paragraph is updated for the new `msgRecv_intro`
  (below).
- F5, F6 and S1 to S3 are R3's (raft-core's files and the `raftlog` snippets). They are not mine.

### A5-completeness

- **F1 (`MessageType.String` lost its spec)**: fixed. There are new **assumed** specs
  `MessageType.String.spec`, `ConfChangeType.String.spec` and `EntryType.String.spec` (files
  `raftpb/{MessageType,ConfChangeType,EntryType}__String.lean`). Each says that for every value,
  under `isPkgInit` of raftpb, the method returns some string and needs nothing else. Each file
  states the reason: the method is untranslated protoc-gen-go code, `EnumStringOf` on the file
  descriptor.
- **F2 (`ProgressTracker.ConfState` returns `confStatePts`)**: fixed in my file.
  `ProgressTracker.ConfState.spec` now returns `RaftPb.confStateFull` (Go always sets `AutoLeave:
  new(p.AutoLeave)`). The post is stronger, so callers of the old one are still served:
  `confStateFull` gives `confStatePts` through the two unfold laws. The rest of the chain is other
  groups' files: see the requests to raft-core and server-core.
- **F3**: the same as provability F4, fixed as above.
- **F4 (`msgRecv` has no producer)**: fixed on raftpb's side with a new law, `msgRecv_intro.spec :
  Proto.mergeDst raftpb.Message.ty p c ∗ ⌜msgIs c m⌝ ⊢ |==> msgRecv p m`.
  - **Fixed differently**: the reviewer suggested a new 2a fact (`freshSlices`). 2a's existing
    `mergeDst` (owned, repeated fields to capacity, submessages writable) is that fact already, so
    no new protobuf vocabulary is needed.
  - The producers are 2a's (`Clone`, `Unmarshal`) and the carriers are rafthttp's and the
    server's: see the requests to grpc-v3rpc, rafthttp and server-core.
- **F5 (`msgPts` cannot hold `Responses`)**: fixed on raftpb's side.
  - There is a new opaque `msgOut p dq m rs`: a `*Message` whose `Responses` holds well-formed
    messages modelled by `rs`. It comes with the laws `msgOut_unfold` and `msgOut_nil` (`msgOut p
    dq m [] ⊣⊢ msgPts p dq m`), and with persistence, timelessness and non-null entries in the
    existing law bundles.
  - `msgFields` is split into `msgCore` (every field but `Responses`) and the empty-`Responses`
    conjunct. Its meaning is unchanged. `msgResps` is the field with responses.
  - The two R1 specs are raft-core's: see the request.
- **Second tier, quorum's sort bound**: the `quorum/Api.lean` header now says where `sortMax`
  actually appears (tracker's `Visit`, `ConfState`, `LearnerNodes`, `VoterNodes`, `QuorumActive`,
  and R3's `readOnly.maybeAdvance`) and where callers discharge it from (`Membership.Valid`, and
  the open receipt-bound decision).

## Coordinator's routed requests from rafthttp

- (1) A law from a decoded or cloned `Message` to `msgRecv`: `RaftPb.msgRecv_intro.spec`. The
  premise it needs from grpc-v3rpc's `Clone`/`Unmarshal` posts is **`Proto.mergeDst
  raftpb.Message.ty p c`** (the fresh-capacity fact; see "Requests to grpc-v3rpc"), together with
  `⌜msgIs c m⌝` (from `msgPts_msgAt` on the sender's side, or `msgEncodes` with `encodes_fun`).
- (2) `MessageType.String.spec`: restored (assumed), `raftpb/MessageType__String.lean`.
- (3) **Done differently**: the law is `msgRecv_lend.spec : msgRecv p m ⊢ ∃ dq, msgPts p dq m ∗
  (msgPts p dq m -∗ msgRecv p m)`. A read share, not `own 1`: with a full `msgPts` lent, the wand
  could get back a message whose `Entries` is another slice, and `msgRecv`'s owned capacity would
  no longer match it, so the `own 1` form is false. The getters work at any fraction.

## Requests to raft-core

1. **`ConfState` fullness through the chain** (A5-completeness F2).
   - `raft.switchToConfig`, `raft.applyConfChange`, `RawNode.ApplyConfChange` and
     `node.ApplyConfChange`: return `RaftPb.confStateFull csp (own 1) cs`, as
     `ProgressTracker.ConfState.spec` now does, instead of `confStatePts`.
   - `MemoryStorage.CreateSnapshot.spec`: take `RaftPb.confStateFull` for its `cs` argument. With
     `confStatePts` it is **false**: Go stores `proto.Clone(cs)`, which is not full when
     `cs.AutoLeave` is nil, yet the post promises `snapshotPts`, which is full.
2. **`newStorageApplyMsg.spec` / `newStorageAppendMsg.spec`** (A5-completeness F5). Their posts
   `msgPts p (own 1) mm` are false: `Responses` is non-empty. Use raftpb's new `msgOut`:
   - `newStorageApplyMsg`: `∃ mm r, msgOut p (own 1) mm [r] ∗ ⌜r.type = MsgStorageApplyResp ∧
     …⌝`;
   - `newStorageAppendMsg`: `∃ mm rs, msgOut p (own 1) mm rs ∗ …`.

   Or give them no spec, as a recorded scope restriction (`ConfigOk` excludes
   `AsyncStorageWrites`).
3. **`RawNode.Bootstrap`'s sketch** (A5 F4/F3): get the entry's bytes from `Marshal.spec`'s
   `noMaps t → bs = marshalOut t c`, with `RaftPb.noMaps_raftpb.spec` and
   `RaftPb.bootEntryData_marshal.spec` (`bootCC_lit` gives `bootCC id ctx c`).
4. **`DescribeConfChange.spec`** (A5-provability F1, R3 part): state it as assumed. It uses
   `strings.Builder` and `fmt.Fprintf` with `%v` of raftpb enums, which have no spec; the old tree
   assumed it too. raftpb's `ConfChangesToString` is now stated the same way. `fmtErrorf.spec` does
   not cover it, because it is `Fprintf`, not `Errorf`.
5. `node.Step` / `RawNode.Step` keep `msgRecv`. Their callers now have an introduction
   (`RaftPb.msgRecv_intro.spec`), once 2a's request below lands.

## Requests to grpc-v3rpc (protobuf `proto`, batch 2a)

1. **`Clone.spec`**: give `mergeDst t p' c` for the clone, in place of `msgAt t p' (own 1) c`
   (which `mergeDst_msgAt` recovers). A clone is a fresh message merged into: protobuf-go
   allocates every repeated field's slice, every bytes field and every submessage, so it owns them
   all to capacity.
2. **`Unmarshal.spec`**: on success, give `mergeDst t p c` (in place of `msgAt t p (own 1) c`).
   `proto.Unmarshal` resets the destination first (`UnmarshalOptions.unmarshal`: `if !o.Merge {
   Reset(m.Interface()) }`), then allocates what it decodes.

Why: A5-completeness F4. raftpb's new `msgRecv_intro` turns a `mergeDst raftpb.Message.ty`
holding a well-formed content into `msgRecv`, the premise of raft's `node.Step`. Without these
posts, no decoded or cloned message reaches `Step`.

## Requests to rafthttp

- The message decoders (`messageDecoder.decodeLimit`, `msgAppV2Decoder.decode`) and the `Process`
  contract (`rafthttp/Api.lean`): deliver `RaftPb.msgRecv p m` (by `RaftPb.msgRecv_intro`, from
  2a's `mergeDst` post above) instead of `msgPts p (own 1) m`. A5-completeness F4.
- `raftpb.MessageType.String` now has a spec (`RaftPb.MessageType.String.spec`). Cite it in the
  sketches of `Transport.Send`, `peer.send`, `remote.send`, the stream reader and
  `pipelineHandler` (A5-completeness F1).

## Requests to server-core

- `EtcdServer.Process`, etcd's `raftNode.Step`: take `RaftPb.msgRecv` (A5-completeness F4).
- Keep `ep.confState` as `RaftPb.confStateFull`, and have `createMergedSnapshotMessage` take it
  (A5-completeness F2). Every source is full: `ApplyConfChange` (once raft-core passes it
  through), and a snapshot's metadata through `snapMetaGo … true`. The merged snapshot message's
  `msgPts` needs it.

## Requests to client-core (optional)

- If `Spec/fmt/` gains a general boundary `fmt.Errorf` (the old `argsOk` with
  `stringMethodSpec`, or the Perennial change below), raftpb's `fmtErrorf.spec` can become an
  instance of it.

## New decisions

- **`fmt.Errorf` with non-`ArgsWf` arguments is a raftpb-local assumed spec.** The old tree had a
  general `Spec/fmt/Errorf.lean` (arguments whose `Error`/`String` have a "returns some string"
  spec). On this branch `Spec/fmt/` is client-core's. I made a narrow local one instead: raftpb
  enums (any verb) and held `*ConfState`s (any verb, read only). The general fix is a Perennial
  change: widen `ArgsWf` to named integer types under `%d`, and to pointer arguments read by
  reflection. It is recorded in the header for `notes/perennial-changes.md`.
- **`msgRecv` is introduced from protobuf's `mergeDst`, not a new "fresh slices" fact.** This
  reuses 2a's existing vocabulary. 2a only has to strengthen two posts (`Clone`, `Unmarshal`), and
  both are true of protobuf-go.
- **Messages with `Responses` get their own predicate (`msgOut`), not a field of `Msg`.** The
  protocol model `Msg` and `msgWf` (no responses) stay as they are, because only the local
  `AsyncStorageWrites` messages carry responses and they are never marshaled. Raft-core can
  instead decline to specify the two helpers as a scope restriction.

## Snippets

`cd examples && go vet ./specreq/raftconf/... ./specreq/raftpb/...`: clean (and `gofmt -l` empty).

## Build

`etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3/{raftpb,quorum,tracker,confchange}`:
**OK (127 modules)**, no warning in these files. The importers in other groups' directories were not
rebuilt here (`msgFields` keeps its meaning; `ProgressTracker.ConfState`'s post changed predicate,
which only raft-core's sketches cite).

## Second pass (coordinator, after grpc-v3rpc's `Proto.norm`)

grpc-v3rpc made `Proto.Content` hold Go values with a wire view `Proto.norm`.
`Clone` now gives `mergeDst t p' (norm c)`, `Unmarshal` gives a canonical `mergeDst t p c`,
`encodes_fun` holds only up to `norm`, and `Equal` compares `norm`s (the converse needs
`noFloats`). Below is what changed in raftpb and how each law fits the restated specs.

- **New law `raftpb_norm.spec`**: every content-to-model relation holds of `norm c` too: `entryIs`,
  `hardStateIs`, `confStateIs` (`full` included), `snapshotIs`, `msgIs`, `confChangeV1Is`,
  `confChangeV2Is`, `singleIs`.
  - Why it holds: raftpb is proto2, so optional fields have explicit presence. `norm` only turns an
    empty repeated field or empty `bytes` into `nil`, and the `List` models do not see that
    difference.
  - Through it, `msgEncodes` and `entryEncodes` survive a round trip: the decoded content is
    canonical, `encodes_fun` gives `norm` equality with the sender's content, and `raftpb_norm`
    carries the model over.
  - **Assumption on 2a's `norm`**: it must keep set proto2 optional fields. Its header speaks only
    of "fields proto3 treats as unset", so 2a should confirm this. Otherwise `csFull` (`AutoLeave`
    set to `false`) would not survive.
- **`confState_ext` restated**: two full contents with one model now have equal `norm`s, not equal
  contents. The old statement was false once contents hold Go values: `nil` and `[]uint64{}`
  voters differ.
- **New law `noFloats_raftpb.spec`**: the nine raftpb types have no float fields. `Equivalent`
  needs `Equal`'s converse direction.
- **`bootCC_facts` gains `norm c = c`**: the bootstrap literal is canonical. Its set fields are
  populated, `Id` is unset and the context is non-empty.
  - `bootEntryData_marshal` is unchanged and still fits: `Marshal.spec` still gives
    `noMaps t → bs = marshalOut t c` for the content `c` the literal holds.
- **`msgRecv_intro`** is unchanged and fits:
  - `Clone`'s `mergeDst (norm c)`, with `msgIs (norm c) m` from `raftpb_norm`;
  - `Unmarshal`'s canonical `mergeDst c`, with `msgIs c m` from `msgEncodes` via `encodes_fun` and
    `raftpb_norm`.

  The docstring says both.
- **`wire_fun` and `decodeConfChange` hold as stated**: `decodeConfChange`'s chosen content and the
  sender's have equal `norm`s, so their models agree by `raftpb_norm`. The `wire_fun` docstring and
  the sketches of `MarshalConfChange` and `ConfState.Equivalent` now cite the `norm` steps, each
  with a `verify-round (second pass)` Changes line.
- **`Model.lean` header**: no longer calls a content "up to `proto.Equal`".
- **Snippets**: the `Specs:` lines of the clone, round-trip, decode and snapshot-clone snippets cite
  `raftpb_norm`. `go vet` and `gofmt` pass.

**Request to grpc-v3rpc**: state in `Proto.norm`'s header that fields with explicit presence (proto2
optional scalars and submessages, proto3 `optional`) keep a set zero value, as protobuf-go's
`Has`/merge do. `raftpb_norm` relies on it.

**Build**: `etc/specs-build.sh --dir` on raftpb, quorum, tracker and confchange: **OK (127
modules)**.
