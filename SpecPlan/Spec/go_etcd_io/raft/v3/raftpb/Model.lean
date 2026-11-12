/-
# raftpb's pure model (batch 3h): raft's protobuf messages as values

`raftpb` (`go.etcd.io/raft/v3/raftpb`, proto2 with protobuf-go v2: optional fields are pointers,
read through nil-safe getters; a missing field reads `0`, `false`, `nil`) holds the messages raft
and its clients exchange: entries, hard states, configurations (`ConfState`), snapshots, messages,
configuration changes. This module is the **pure** part of the package's vocabulary (the resources
and laws are `Api.lean`'s): the values a client of raftpb computes with, the protobuf content of a
message as such a value (`entryOf`, ...), and the wire model (`decodeConfChange`, `msgEncodes`).

## Shared with raft (R1, R2, R3, R4)

The structures below are field for field R1's (`SpecPlan/Spec/go_etcd_io/raft/v3/Model.lean`: `LogEntry`,
`HardState`, `ConfState`, `Snapshot`, `ConfChangeV1`, `ConfChangeSingle`, `ConfChangeV2`,
`ConfChangeI`, `Msg`, the enumerations). This module imports nothing of raft's, so that R1's
`Model.lean` can import it: at integration R1's structures become abbreviations of these (`abbrev
LogEntry := RaftPb.LogEntry`, ...: the same field names), its opaque `decodeConfChange` and
`bootEntryData` become these definitions, and R4's `ConfChange.Single` is `ConfChangeSingle`
(`type`, `nodeId`). Same precedent as tracker's `Membership` (`tracker/Model.lean`).

## Contents (the wire model)

A message's protobuf content is protobuf's `Proto.Content` (batch 2a, `proto/Api.lean`): a value,
the message's Go field values and its unknown fields, independent of any address or heap; the wire
carries its view `Proto.norm c` (empty repeated and `bytes` fields as `nil`; raftpb is proto2, so
set optional fields keep their presence), and every relation below survives it (`raftpb_norm`,
`Api.lean`). What raft reads of a content is a **function** of it, one per message type: `entryOf c`,
`hardStateOf c`, `confStateOf c`, `snapshotOf c`, `msgOf c`, `confChangeOf c`, `confChangeV2Of c`,
`singleOf c` (the getters' values: presence is forgotten, as the getters forget it), and a few
predicates of the content that the getters do not show but raft relies on:

* `plain c`: no unknown fields, anywhere in the message (every message raft or its clients build;
  a decoded message is plain iff the encoded one was). It makes a content a function of its Go
  fields (`proto.Equal` compares presence, values and unknown bytes), which `ConfState.Equivalent`
  (`proto.Equal` of two sorted clones) and the size bounds below need.
* `csFull c`, `snapFull c`: every pointer field `EnsureConfState`/`EnsureSnapshot` would
  fill is set (`AutoLeave`; the metadata, its `ConfState`, `Index`, `Term`). raft's snapshots are
  always full (`MemoryStorage` and raft ensure them before sharing them), and raft calls `Ensure*`
  on shared read-only snapshots, which must then write nothing.
* `msgEntryIndexes c`, `msgSnapFull c`, `msgNoResponses c`: a message's entries' `Index` fields
  (which `Msg` forgets: a log entry's index is its position), whether its snapshot (if set) is full,
  and that `Responses` is empty (`Msg` has no responses: only `AsyncStorageWrites`' local messages carry
  them, `Api.lean`'s `msgOut`). `msgWf` combines them with the index rule of a `MsgApp` (its entries at
  `index + 1, index + 2, ...`).

These readers are opaque functions: any function is consistent, and their meaning is fixed by the
relation laws of `Api.lean` (`entryPts p dq i e ⊣⊢ ∃ c, Proto.msgAt Entry.ty p dq c ∗ ⌜...⌝`)
together with the field-level unfold laws. **No law equates two contents held at different
addresses or in different heaps** (the old `pbEnc` keyed by address, `specs-ref/notes/
per-type-blockers.md` (b)); no statement is quantified over a caller-built wire model (the old
`PbType`, `specs-ref/notes/pbenc-ok-inconsistent.md`): the only wire relation is protobuf's
`Proto.encodes`, and decoding is a function because `encodes` is (`Proto.encodes_fun`).

* `decodeConfChange t bs`: what `proto.Unmarshal` of an entry's bytes into a `ConfChange` (`t =
  EntryConfChange`) or a `ConfChangeV2` (`EntryConfChangeV2`) gives, when the bytes encode a content
  of that type (`confChangeV1Is`/`confChangeV2Is`: plain, so it nests less than protobuf's recursion
  limit); `none` otherwise. Defined from
  `Proto.encodes` (classical choice of the unique content).
* `msgEncodes bs m`, `entryEncodes bs i e`: `bs` is a wire encoding of a well-formed message
  modelled by `m` (an entry at index `i`): what a transport (rafthttp, 2f) carries with `msgSent`.
* `bootCC id ctx c` (opaque, a relation: protobuf's `Content` type has no element this package could
  name): `c` is the content of the `ConfChange{Type: AddNode, NodeId: id, Context: ctx}` that
  `RawNode.Bootstrap` builds (`Id` unset); `bootEntryData id ctx` (opaque bytes): what
  `proto.Marshal` gives it. Determinism (every founder appends the same bytes) is protobuf-go's: a
  message without map fields marshals to a function of its content (2a's `Proto.marshalOut`):
  `bootEntryData id ctx` is `Proto.marshalOut ConfChange.ty c` for the `c` with `bootCC id ctx c`
  (law `bootEntryData_marshal`, with `noMaps_raftpb`, `Api.lean`).

**What a content of each type satisfies** (`entryIs`, `hardStateIs`, `confStateIs`, `snapshotIs`,
`msgIs`, `confChangeV1Is`, `confChangeV2Is`, `singleIs`): the readers' values, plainness (and
fullness, well-formedness), and three facts protobuf's boundary asks of the owner of a type
(`proto/Api.lean`): `Proto.marshalOk` (raftpb has no `string` and no required field: every content
marshals), the nesting depth (raftpb is not recursive once `Responses` is empty: at most four
levels, `Message`/`Snapshot`/`SnapshotMetadata`/`ConfState`), and the encoded size bounded by the
model (below). The relation laws of `Api.lean` tie each Go ownership predicate to `Proto.msgAt` of a
content satisfying its `*Is`.

## Sizes

`proto.Marshal` takes `Proto.Content.fits` (an encoding below `2 ^ 48` bytes, Go's largest
allocation). A plain content's encoded size is bounded by its model (`Msg.wireBound`,
`ConfChangeI.wireBound`, laws `*_encSize` in `Api.lean`): generous constants per field (a varint is
at most 10 bytes, a tag at most 2, a length prefix at most 10) plus the byte slices' lengths.
-/
module

public import GeneratedProof.go_etcd_io.raft.v3.raftpb
public import SpecPlan.Spec.google_golang_org.protobuf.proto.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI

/-! ## Enumerations -/

/-- `EntryType`'s values. -/
def EntryNormal : w32 := W32 0
def EntryConfChange : w32 := W32 1
def EntryConfChangeV2 : w32 := W32 2

/-- `MessageType`'s values. -/
def MsgHup : w32 := W32 0
def MsgBeat : w32 := W32 1
def MsgProp : w32 := W32 2
def MsgApp : w32 := W32 3
def MsgAppResp : w32 := W32 4
def MsgVote : w32 := W32 5
def MsgVoteResp : w32 := W32 6
def MsgSnap : w32 := W32 7
def MsgHeartbeat : w32 := W32 8
def MsgHeartbeatResp : w32 := W32 9
def MsgUnreachable : w32 := W32 10
def MsgSnapStatus : w32 := W32 11
def MsgCheckQuorum : w32 := W32 12
def MsgTransferLeader : w32 := W32 13
def MsgTimeoutNow : w32 := W32 14
def MsgReadIndex : w32 := W32 15
def MsgReadIndexResp : w32 := W32 16
def MsgPreVote : w32 := W32 17
def MsgPreVoteResp : w32 := W32 18
def MsgStorageAppend : w32 := W32 19
def MsgStorageAppendResp : w32 := W32 20
def MsgStorageApply : w32 := W32 21
def MsgStorageApplyResp : w32 := W32 22
def MsgForgetLeader : w32 := W32 23

/-- `ConfChangeType`'s values. -/
def ConfChangeAddNode : w32 := W32 0
def ConfChangeRemoveNode : w32 := W32 1
def ConfChangeUpdateNode : w32 := W32 2
def ConfChangeAddLearnerNode : w32 := W32 3

/-- `ConfChangeTransition`'s values. -/
def ConfChangeTransitionAuto : w32 := W32 0
def ConfChangeTransitionJointImplicit : w32 := W32 1
def ConfChangeTransitionJointExplicit : w32 := W32 2

/-! ## The messages' models (R1's, field for field) -/

/-- `Entry` without its index (the getters' `Term`, `Type`, `Data`). -/
structure LogEntry where
  term : w64
  type : w32
  data : List w8
deriving DecidableEq, Inhabited

/-- `HardState`. -/
structure HardState where
  term : w64
  vote : w64
  commit : w64
deriving DecidableEq, Inhabited

def HardState.empty : HardState := ⟨W64 0, W64 0, W64 0⟩

/-- `ConfState`: the four id lists as Go holds them (order and repeats kept), `AutoLeave`. -/
structure ConfState where
  voters : List w64
  learners : List w64
  votersOutgoing : List w64
  learnersNext : List w64
  autoLeave : Bool
deriving Inhabited

def ConfState.empty : ConfState := ⟨[], [], [], [], false⟩

/-- Each list at most `2 ^ 62` long (`slices.Sort`'s bound: `Equivalent` sorts them). Every
configuration raft builds meets it (R4's `Membership.Valid`: fewer than `2 ^ 62` ids). -/
def ConfState.lenOk (cs : ConfState) : Prop :=
  cs.voters.length ≤ 2 ^ 62 ∧ cs.learners.length ≤ 2 ^ 62 ∧ cs.votersOutgoing.length ≤ 2 ^ 62 ∧
  cs.learnersNext.length ≤ 2 ^ 62

/-- **Two `ConfState`s list the same configuration** (what `Equivalent` checks): each list a
permutation of the other's, the same `AutoLeave`. -/
def ConfState.Equiv (a b : ConfState) : Prop :=
  a.voters.Perm b.voters ∧ a.learners.Perm b.learners ∧
  a.votersOutgoing.Perm b.votersOutgoing ∧ a.learnersNext.Perm b.learnersNext ∧
  a.autoLeave = b.autoLeave

/-- `SnapshotMetadata`. -/
structure SnapMeta where
  index : w64
  term : w64
  conf : ConfState
deriving Inhabited

/-- `Snapshot` with its metadata (R1's flat record). -/
structure Snapshot where
  index : w64
  term : w64
  conf : ConfState
  data : List w8
deriving Inhabited

def Snapshot.empty : Snapshot := ⟨W64 0, W64 0, ConfState.empty, []⟩

def Snapshot.meta (s : Snapshot) : SnapMeta := ⟨s.index, s.term, s.conf⟩

/-- `ConfChange` (the legacy change). -/
structure ConfChangeV1 where
  type : w32
  nodeId : w64
  context : List w8
  id : w64
deriving Inhabited

/-- `ConfChangeSingle`. -/
structure ConfChangeSingle where
  type : w32
  nodeId : w64
deriving Inhabited

/-- `ConfChangeV2`. -/
structure ConfChangeV2 where
  transition : w32
  changes : List ConfChangeSingle
  context : List w8
deriving Inhabited

/-- `ConfChangeI`: either kind. -/
inductive ConfChangeI where
  | v1 (c : ConfChangeV1)
  | v2 (c : ConfChangeV2)
deriving Inhabited

/-- The entry type `MarshalConfChange` gives a change. -/
def ConfChangeI.entryType : ConfChangeI → w32
  | .v1 _ => EntryConfChange
  | .v2 _ => EntryConfChangeV2

/-- `ConfChange.AsV2()`: one change of the same type and node, transition `Auto`, the context. -/
def ConfChangeV1.asV2 (c : ConfChangeV1) : ConfChangeV2 :=
  ⟨ConfChangeTransitionAuto, [⟨c.type, c.nodeId⟩], c.context⟩

/-- `ConfChangeI.AsV2()`. -/
def ConfChangeI.asV2 : ConfChangeI → ConfChangeV2
  | .v1 c => c.asV2
  | .v2 c => c

/-- `ConfChangeV2.LeaveJoint()`: transition `Auto` and no change. -/
def ConfChangeV2.leaveJoint (c : ConfChangeV2) : Bool :=
  decide (c.transition = ConfChangeTransitionAuto ∧ c.changes = [])

/-- `ConfChangeV2.EnterJoint()`: `(autoLeave, ok)`; `none` where it panics (an unknown transition
that is not `Auto` with at most one change). -/
def ConfChangeV2.enterJoint (c : ConfChangeV2) : Option (Bool × Bool) :=
  if c.transition ≠ ConfChangeTransitionAuto ∨ 1 < c.changes.length then
    if c.transition = ConfChangeTransitionAuto ∨ c.transition = ConfChangeTransitionJointImplicit
    then some (true, true)
    else if c.transition = ConfChangeTransitionJointExplicit then some (false, true)
    else none
  else some (false, false)

/-- `ConfChangesToString`'s letter of a change type (`unknown` for another). -/
def ccLetter (t : w32) : List w8 :=
  if t = ConfChangeAddNode then [W8 118]            -- 'v'
  else if t = ConfChangeAddLearnerNode then [W8 108] -- 'l'
  else if t = ConfChangeRemoveNode then [W8 114]     -- 'r'
  else if t = ConfChangeUpdateNode then [W8 117]     -- 'u'
  else [W8 117, W8 110, W8 107, W8 110, W8 111, W8 119, W8 110] -- "unknown"

/-- **A raft message** (`Message`), the protocol's content (R1's `Msg`; `Responses` left out). -/
structure Msg where
  type : w32
  to : w64
  src : w64
  term : w64
  logTerm : w64
  index : w64
  entries : List LogEntry
  commit : w64
  vote : w64
  snapshot : Option Snapshot
  reject : Bool
  rejectHint : w64
  context : List w8
deriving Inhabited

/-- The `Index` fields of a well-formed message's entries: a `MsgApp`'s follow its `Index` (the
entry before them); any other type's are unconstrained (`none`: a proposal's entries are numbered
only when the leader appends copies of them). -/
def Msg.entryIndexes (m : Msg) : Option (List w64) :=
  if m.type = MsgApp then
    some ((List.range m.entries.length).map (fun (j : Nat) => W64 ((uint.nat m.index + 1 + j : Nat) : Int)))
  else none

/-! ## Sizes -/

/-- A bound on the encoded size of a plain `ConfState` of model `cs`. -/
def ConfState.wireBound (cs : ConfState) : Nat :=
  32 + 12 * (cs.voters.length + cs.learners.length + cs.votersOutgoing.length +
    cs.learnersNext.length)

/-- A bound on the encoded size of a plain, full `Snapshot` of model `s`. -/
def Snapshot.wireBound (s : Snapshot) : Nat := 96 + s.data.length + s.conf.wireBound

/-- A bound on the encoded size of a well-formed message of model `m` (each entry with its index). -/
def Msg.wireBound (m : Msg) : Nat :=
  256 + m.context.length + (m.entries.map (fun e => 64 + e.data.length)).sum +
    (match m.snapshot with | none => 0 | some s => 16 + s.wireBound)

/-- A bound on the encoded size of a plain configuration change of model `c`. -/
def ConfChangeI.wireBound : ConfChangeI → Nat
  | .v1 c => 64 + c.context.length
  | .v2 c => 64 + c.context.length + 32 * c.changes.length

/-! ## Contents: what a message's protobuf content holds -/

section content
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The `Index` an `Entry` content holds (`0` if unset). -/
opaque entryIndexOf : Proto.Content → w64
/-- The `Term`, `Type`, `Data` an `Entry` content holds. -/
opaque entryOf : Proto.Content → LogEntry
/-- The `HardState` a content holds. -/
opaque hardStateOf : Proto.Content → HardState
/-- The `ConfState` a content holds. -/
opaque confStateOf : Proto.Content → ConfState
/-- The `ConfState` content has `AutoLeave` set. -/
opaque csFull : Proto.Content → Prop
/-- The `SnapshotMetadata` a content holds. -/
opaque snapMetaOf : Proto.Content → SnapMeta
/-- The `Snapshot` a content holds (its metadata's fields flattened, zero where unset). -/
opaque snapshotOf : Proto.Content → Snapshot
/-- The `Snapshot` content has its metadata, the metadata's `ConfState`, `Index`, `Term` and the
`ConfState`'s `AutoLeave` set. -/
opaque snapFull : Proto.Content → Prop
/-- The `Message` a content holds (its snapshot `none` iff the field is unset). -/
opaque msgOf : Proto.Content → Msg
/-- The `Index` fields of a `Message` content's entries. -/
opaque msgEntryIndexes : Proto.Content → List w64
/-- The `Message` content's snapshot, if set, is full. -/
opaque msgSnapFull : Proto.Content → Prop
/-- The `Message` content has no `Responses`. -/
opaque msgNoResponses : Proto.Content → Prop
/-- The `ConfChange` a content holds. -/
opaque confChangeOf : Proto.Content → ConfChangeV1
/-- The `ConfChangeV2` a content holds. -/
opaque confChangeV2Of : Proto.Content → ConfChangeV2
/-- The `ConfChangeSingle` a content holds. -/
opaque singleOf : Proto.Content → ConfChangeSingle
/-- **No unknown fields anywhere in the content.** -/
opaque plain : Proto.Content → Prop

/-- **A well-formed message content** (every one raft builds or a client builds for raft): plain,
its snapshot full, no responses, a `MsgApp`'s entries numbered from its `Index + 1`. -/
def msgWf (c : Proto.Content) : Prop :=
  plain c ∧ msgSnapFull c ∧ msgNoResponses c ∧
  ∀ ixs, (msgOf c).entryIndexes = some ixs → msgEntryIndexes c = ixs

/-- What an `Entry` content at index `i` modelled by `e` satisfies. -/
def entryIs (c : Proto.Content) (i : w64) (e : LogEntry) : Prop :=
  plain c ∧ entryIndexOf c = i ∧ entryOf c = e ∧ Proto.marshalOk c ∧ Proto.depth c ≤ 1 ∧
  Proto.encSize c ≤ 64 + e.data.length

/-- What a `HardState` content satisfies. -/
def hardStateIs (c : Proto.Content) (hs : HardState) : Prop :=
  plain c ∧ hardStateOf c = hs ∧ Proto.marshalOk c ∧ Proto.depth c ≤ 1 ∧ Proto.encSize c ≤ 64

/-- What a `ConfState` content satisfies (`full`: `AutoLeave` set). -/
def confStateIs (c : Proto.Content) (cs : ConfState) (full : Bool) : Prop :=
  plain c ∧ confStateOf c = cs ∧ cs.lenOk ∧ (full = true → csFull c) ∧ Proto.marshalOk c ∧
  Proto.depth c ≤ 1 ∧ Proto.encSize c ≤ cs.wireBound

/-- What a `Snapshot` content satisfies (`full`: every field `EnsureSnapshot` fills set). -/
def snapshotIs (c : Proto.Content) (s : Snapshot) (full : Bool) : Prop :=
  plain c ∧ snapshotOf c = s ∧ (full = true → snapFull c) ∧ Proto.marshalOk c ∧
  Proto.depth c ≤ 3 ∧ Proto.encSize c ≤ s.wireBound

/-- What a `Message` content satisfies. -/
def msgIs (c : Proto.Content) (m : Msg) : Prop :=
  msgWf c ∧ msgOf c = m ∧ Proto.marshalOk c ∧ Proto.depth c ≤ 4 ∧ Proto.encSize c ≤ m.wireBound

/-- What a `ConfChange` content satisfies. -/
def confChangeV1Is (c : Proto.Content) (cc : ConfChangeV1) : Prop :=
  plain c ∧ confChangeOf c = cc ∧ Proto.marshalOk c ∧ Proto.depth c ≤ 1 ∧
  Proto.encSize c ≤ (ConfChangeI.v1 cc).wireBound

/-- What a `ConfChangeV2` content satisfies. -/
def confChangeV2Is (c : Proto.Content) (cc : ConfChangeV2) : Prop :=
  plain c ∧ confChangeV2Of c = cc ∧ Proto.marshalOk c ∧ Proto.depth c ≤ 2 ∧
  Proto.encSize c ≤ (ConfChangeI.v2 cc).wireBound

/-- What a `ConfChangeSingle` content satisfies. -/
def singleIs (c : Proto.Content) (s : ConfChangeSingle) : Prop :=
  plain c ∧ singleOf c = s ∧ Proto.marshalOk c ∧ Proto.depth c ≤ 1 ∧ Proto.encSize c ≤ 32

/-! ## The wire model -/

open go_etcd_io.raft.v3 Classical in
/-- **What the bytes of a conf-change entry of type `t` decode to** (see the header). -/
def decodeConfChange (t : w32) (bs : List w8) : Option ConfChangeI :=
  if t = EntryConfChange then
    if h : ∃ c cc, Proto.encodes raftpb.ConfChange.ty c bs ∧ confChangeV1Is c cc
    then some (.v1 (confChangeOf (Classical.choose h))) else none
  else if t = EntryConfChangeV2 then
    if h : ∃ c cc, Proto.encodes raftpb.ConfChangeV2.ty c bs ∧ confChangeV2Is c cc
    then some (.v2 (confChangeV2Of (Classical.choose h))) else none
  else none

open go_etcd_io.raft.v3 in
/-- **`bs` encodes a well-formed message modelled by `m`** (what a transport carries). -/
def msgEncodes (bs : List w8) (m : Msg) : Prop :=
  ∃ c, Proto.encodes raftpb.Message.ty c bs ∧ msgIs c m

open go_etcd_io.raft.v3 in
/-- **`bs` encodes a plain entry at index `i` modelled by `e`** (rafthttp's `msgappv2` entries). -/
def entryEncodes (bs : List w8) (i : w64) (e : LogEntry) : Prop :=
  ∃ c, Proto.encodes raftpb.Entry.ty c bs ∧ entryIs c i e

/-- **`c` is the content of the bootstrap `ConfChange`** for peer `id` with context `ctx`
(`AddNode`, the node, the context set; `Id` unset; plain): at most one (`bootCC_facts`). -/
opaque bootCC (id : w64) (ctx : List w8) (c : Proto.Content) : Prop

/-- **The bytes of a bootstrap entry** (see the header): `proto.Marshal` of the `bootCC id ctx`
content. -/
opaque bootEntryData (id : w64) (ctx : List w8) : List w8

end content

end RaftPb
end EtcdGrove
end Perennial
