/-
# raftpb's Go ownership (batch 3h): the vocabulary

The resources and laws of raft's protobuf messages; the pure part is `Model.lean`. Who uses them:
raft's node API (R1: `Ready`, `Storage`, `Step`, `ProposeConfChange`, `ApplyConfChange`), its core
(R2: building, stepping and sending messages), its log (R3: entries, snapshots), confchange (R4:
`ConfState`, the changes), rafthttp (2f: messages on the wire), etcd's server (2d, 2e: snapshots,
`ConfState`s, conf changes in entries).

## The predicates

One opaque **ownership predicate per message type**, over the model of `Model.lean`:

| predicate | Go value | R1/R2/R3/R4's provisional name |
|---|---|---|
| `entryPts p dq i e` | `*Entry` at index `i` | (R3) `entryRO p k e` = `entryPts p □ (W64 k) e` |
| `hardStatePts p dq hs` | `*HardState` | (R1) `hardStatePts` |
| `confStatePts p dq cs` | `*ConfState`, any presence | (R1) `confStatePts` |
| `confStateFull p dq cs` | `*ConfState`, `AutoLeave` set | (none: what `EnsureConfState` returns) |
| `snapshotPts p dq s` | `*Snapshot`, full (`Ensure*` would write nothing) | (R1) `snapshotPts` |
| `snapshotRaw p dq s` | `*Snapshot`, any presence | (none: what `EnsureSnapshot` takes) |
| `msgPts p dq m` | `*Message`, well-formed | (R1) `msgPts` |
| `msgRecv p m` | `*Message` received: `msgPts` at `own 1`, its `Entries` capacity owned | (I2; the old `msgPtsC … cap`) |
| `msgOut p dq m rs` | `*Message` with `Responses` `rs` (`AsyncStorageWrites`' local messages) | (verify round) |
| `confChangeV1Pts p dq c`, `confChangeV2Pts p dq c`, `singlePts p dq s` | `*ConfChange`, `*ConfChangeV2`, `*ConfChangeSingle` | |

and transparent definitions over them: `entryRO p k e`, `entriesRO sl k es` (R1's, R3's: a slice of
read-only entries numbered from `k`), `entryPtrs sl dq es` (R2's: entries of any index),
`confChangePts v dq c` (R1's: a `ConfChangeI` interface value), `ccsPts sl dq cs` (R4's: a
`[]*ConfChangeSingle`), and the Go-level helpers the unfold laws are written with (`optCell`,
`confStateGo`, `snapMetaGo`, `snapshotGo`, `pbRest`).

**What `dq` covers** (the Go code's sharing decides it). A predicate at `dq` owns the message
struct's own fields at `dq`, and:
* everything raft ever shares between messages **read-only for good** (`□`): every scalar cell an
  optional field points to (raft builds `&pb.Message{To: m.From}`: the reply's `To` *is* the
  request's `From` cell; nobody writes through such a pointer, every write replaces it), every byte
  slice (`Data`, `Context`: raft and its clients keep the bytes they hand over), a message's entries
  (its `Entries` slice and the `*Entry`s: a `MsgApp` carries the log's own entries) and its snapshot
  (a `Ready`'s messages share the `Ready`'s snapshot);
* at `dq`, what the code writes in place: a snapshot's `SnapshotMetadata` and its `ConfState`
  (`MemoryStorage.CreateSnapshot` sets `Metadata.Index`; `EnsureConfState` sets `AutoLeave`), a
  `ConfState`'s four id slices (`Equivalent` sorts its clones' slices in place), a `ConfChangeV2`'s
  `Changes` slice and its singles.

`pbRest t p dq` is the protobuf bookkeeping of a message (`state`, `sizeCache`, which protobuf-go
stores atomically, and an empty `unknownFields`: raft's messages are plain). Opaque; its intro law
`pbRest_zero` is what a composite literal `&pb.Message{...}` gives.

**Intended realization.** Each predicate is its unfold law's right side; `Proto.msgAt T.ty p dq c`
(protobuf's opaque holding, 2a) is realized for each raftpb type `T` by the same field-level
predicate, with the content `c` the value of those fields (presence included) and no unknown
fields, so that the relation laws (`entryPts_msgAt`, ...) hold with the readers of `Model.lean`
defined from the fields. The laws below are the obligations of that realization.

**No raftpb message is a `proto.Merge` destination** (round 1, F1): `Merge` writes in place (it
merges into set submessages and appends into repeated fields' spare capacity), and these predicates
hold submessages read-only for good and slices without their capacity (a `MsgApp`'s entries are a
sub-slice of the leader's log). No law here gives protobuf's merge-destination premise (2a's
`Proto.mergeDst`, which replaced 3h's `mergeDstOk` at integration I3) for a raftpb type; raft and
etcd never merge raft messages. The other direction is used: a `*Message` that *is* a merge
destination (protobuf's `Clone` and `Unmarshal` allocate one, requested of 2a at the verify round)
is a received message (`msgRecv_intro`).

**A homogeneous cluster** (round 1, second tier 8): `msgPts` requires a set snapshot to be full.
The Go comment on `Message.Snapshot` allows peers running older binaries to send a non-nil, empty
snapshot; such a decoded message has no `msgPts` (2f's decoder cannot deliver it). A scope
restriction, stated.

## Laws

Persistence, timelessness, non-null (`raftpb_persistent`, `raftpb_timeless`, `raftpb_ne_null`);
the **unfold laws** (field by field: what a client reads and, at `own 1`, writes; R2's field writes
of `From`/`To` and R3's `entriesRO` indexing are instances); the **relation laws** to `Proto.msgAt`
(what `proto.Clone`, `Marshal`, `Unmarshal`, `Size`, `Equal` need: each of those specs is 2a's, over
`msgAt`); `raftpb_norm` and `noFloats_raftpb` (the models survive protobuf's wire view `Proto.norm`;
`proto.Equal`'s converse); `msgRecv_intro` (a fresh decoded or cloned message is a received one), `msgRecv_lend`
(a read share of it); `msgOut_unfold`,
`msgOut_nil` (a message with responses); `pbRest_zero`; the content laws `confState_ext` (for
`Equivalent`), `bootCC_*` and `bootEntryData_marshal` with `noMaps_raftpb` (the bootstrap entry:
its bytes are `Marshal`'s output, the same at every founder), `decodeConfChange_empty` (the
auto-leave entry), `wire_fun` (`msgEncodes`, `entryEncodes`: decoding is a function of the bytes).

## Assumed specs (trust boundary)

`FmtErrorf.lean` (`fmtErrorf.spec`: `fmt.Errorf` with raftpb enum and `*ConfState` arguments,
which Perennial's `ArgsWf` excludes; used by `Equivalent` and confchange's `Changer.apply`),
`MessageType.String`, `ConfChangeType.String`, `EntryType.String` (untranslated protoc-gen-go
methods), `ConfChangesToString` (translated, but over `strings.Builder` and `fmt.Fprintf`, which
have no spec).

## Requirement snippets

`examples/specreq/raftpb/`: `messages.go` (getters through `nil`; building and stepping a message;
a reply sharing the request's `From` cell; field writes), `confchange.go` (marshal and decode a
change, `AsV2`, `EnterJoint`/`LeaveJoint`, the auto-leave entry, `Equivalent` of two orders),
`snapshot.go` (`EnsureSnapshot` of a built snapshot, clone, `IsEmptySnap`-style reads, bootstrap
bytes deterministic).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.raftpb.Model
public import SpecPlan.Spec.PkgInit.go_etcd_io.raft.v3.raftpb

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-! ## Go-level helpers -/

/-- An optional scalar field's pointer `fp`: `nil` (the getter reads the default `d`), or a
read-only cell holding `v`. -/
def optCell {V : Type} [TypedPointsto (GF := GF) V] (fp : Loc) (v d : V) : IProp GF :=
  iprop(⌜fp = null ∧ v = d⌝ ∨ fp ↦□ v)

/-- **The protobuf bookkeeping of the message of Go type `t` at `p`** (`state`, `sizeCache`, an
empty `unknownFields`), fraction `dq`. Opaque. -/
opaque pbRest [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Type) (p : Loc) (dq : DFrac) : IProp GF := iprop(True)

/-! ## The ownership predicates (opaque) -/

/-- **An `*Entry` at `p` with index `i`** (its `Index` field's value) and term, type, data `e`. -/
opaque entryPts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (i : w64) (e : LogEntry) : IProp GF := iprop(True)

/-- **A `*HardState`.** -/
opaque hardStatePts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (hs : HardState) : IProp GF := iprop(True)

/-- **A `*ConfState`** (its `AutoLeave` may be unset: read `false`). -/
opaque confStatePts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (cs : ConfState) : IProp GF := iprop(True)

/-- **A `*ConfState` with `AutoLeave` set** (`EnsureConfState` writes nothing). -/
opaque confStateFull [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (cs : ConfState) : IProp GF := iprop(True)

/-- **A full `*Snapshot`**: its metadata, the metadata's `ConfState`, `Index`, `Term` and the conf
state's `AutoLeave` set (`EnsureSnapshot` writes nothing). raft's and `MemoryStorage`'s. -/
opaque snapshotPts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (s : Snapshot) : IProp GF := iprop(True)

/-- **A `*Snapshot`, any presence** (what `EnsureSnapshot` takes). -/
opaque snapshotRaw [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (s : Snapshot) : IProp GF := iprop(True)

/-- **A well-formed `*Message`** (`msgWf`): no `Responses`, its snapshot (if any) full, a `MsgApp`'s
entries numbered from `Index + 1`. -/
opaque msgPts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : Msg) : IProp GF := iprop(True)

/-- **A received `*Message`** (one stepped into raft from outside: what rafthttp's decoders and a
`proto.Clone` deliver): `msgPts` at `own 1` with the spare capacity of its `Entries` slice owned
(fresh, as protobuf's unmarshalling and cloning allocate it). A message raft built has no spare
capacity (`raftLog.slice` clips, given the `Storage` contract), but `msgPts`, shared read-only, does
not record it; an in-process transport must clone it (`nonissues/raft-msgapp-inprocess-aliasing.md`). (Integration I2, the coordinator's
decision; the old proof's `msgPtsC … cap`.) -/
opaque msgRecv [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (m : Msg) : IProp GF := iprop(True)

/-- **A local `*Message` with responses** (`AsyncStorageWrites`' `MsgStorageAppend`/`MsgStorageApply`,
whose `Responses` raft fills: `rawnode.go:254-258`, `:380`): `msgPts`'s fields of `m` (snapshot,
entries, cells as there) and `Responses` holding well-formed messages modelled by `rs`
(`msgOut_unfold`); with no response it is `msgPts` (`msgOut_nil`). Such a message is never
marshaled (it goes to the local storage threads), so it has no relation to `Proto.msgAt`.
(Verify round, A5-completeness F5.) -/
opaque msgOut [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : Msg) (rs : List Msg) : IProp GF := iprop(True)

/-- **A `*ConfChange`.** -/
opaque confChangeV1Pts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (c : ConfChangeV1) : IProp GF := iprop(True)

/-- **A `*ConfChangeV2`.** -/
opaque confChangeV2Pts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (c : ConfChangeV2) : IProp GF := iprop(True)

/-- **A `*ConfChangeSingle`.** -/
opaque singlePts [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (s : ConfChangeSingle) : IProp GF := iprop(True)

/-! ## Definitions over them -/

/-- **One read-only entry at index `k`** (R3's `entryRO`). Persistent. -/
def entryRO (p : Loc) (k : Nat) (e : LogEntry) : IProp GF := entryPts p DFrac.discard (W64 k) e

/-- **A slice of read-only entries, the first at index `k`** (R1's `entriesRO`): the slice and the
entries read-only for good. Persistent. -/
def entriesRO (sl : GoSlice) (k : Nat) (es : List LogEntry) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*□ ps ∗ [∗list] j ↦ p; e ∈ ps; es, entryRO p (k + j) e)

/-- **A slice of entries of any indices** (R2's `entryPtrs`: a proposal's, before numbering), `dq`
of the slice and of each entry's struct. -/
def entryPtrs (sl : GoSlice) (dq : DFrac) (es : List LogEntry) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*{dq} ps ∗ [∗list] p; e ∈ ps; es, ∃ i, entryPts p dq i e)

/-- **A `ConfChangeI` interface value holding change `c`**: a `*ConfChange` or a `*ConfChangeV2`
(R1's `confChangePts`). -/
def confChangePts (v : GoInterface) (dq : DFrac) : ConfChangeI → IProp GF
  | .v1 c => iprop(∃ p : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p⌝ ∗ confChangeV1Pts p dq c)
  | .v2 c => iprop(∃ p : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #p⌝ ∗ confChangeV2Pts p dq c)

/-- **A `[]*ConfChangeSingle`** (R4's `ccsPts`, over `ConfChangeSingle`, R4's `ConfChange.Single`):
the slice and each single at `dq`. -/
def ccsPts (sl : GoSlice) (dq : DFrac) (cs : List ConfChangeSingle) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*{dq} ps ∗ [∗list] p; s ∈ ps; cs, singlePts p dq s)

/-- **A message's `Entries` slice**: read-only for good, its entries read-only, each at its index
(a `MsgApp`'s at `Index + 1, Index + 2, ...`: `msgEnts_app`; another type's at any). Persistent. -/
def msgEnts (sl : GoSlice) (m : Msg) : IProp GF :=
  iprop(∃ eps : List Loc, sl ↦*□ eps ∗
    [∗list] j ↦ q; e ∈ eps; m.entries, ∃ i : w64, entryPts q DFrac.discard i e ∗
      ⌜∀ ixs, m.entryIndexes = some ixs → ixs[j]? = some i⌝)

/-- A `*ConfState`'s fields (`full`: `AutoLeave` set), its lists within `slices.Sort`'s bound. -/
def confStateGo (p : Loc) (dq : DFrac) (cs : ConfState) (full : Bool) : IProp GF :=
  iprop(∃ (vs ls vos lns : GoSlice) (ap : Loc), pbRest raftpb.ConfState p dq ∗
    p.[raftpb.ConfState, go!"Voters"] ↦{dq} vs ∗ vs ↦*{dq} cs.voters ∗
    p.[raftpb.ConfState, go!"Learners"] ↦{dq} ls ∗ ls ↦*{dq} cs.learners ∗
    p.[raftpb.ConfState, go!"VotersOutgoing"] ↦{dq} vos ∗ vos ↦*{dq} cs.votersOutgoing ∗
    p.[raftpb.ConfState, go!"LearnersNext"] ↦{dq} lns ∗ lns ↦*{dq} cs.learnersNext ∗
    p.[raftpb.ConfState, go!"AutoLeave"] ↦{dq} ap ∗
    (if full then ap ↦□ cs.autoLeave else optCell ap cs.autoLeave false) ∗ ⌜cs.lenOk⌝)

/-- A `*SnapshotMetadata`'s fields (`full`: its `ConfState`, `Index`, `Term` set, the conf state
full). -/
def snapMetaGo (p : Loc) (dq : DFrac) (sm : SnapMeta) (full : Bool) : IProp GF :=
  iprop(∃ (cp ip tp : Loc), pbRest raftpb.SnapshotMetadata p dq ∗
    p.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} cp ∗
    p.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} ip ∗
    p.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} tp ∗
    if full then confStateFull cp dq sm.conf ∗ ip ↦□ sm.index ∗ tp ↦□ sm.term
    else (⌜cp = null ∧ sm.conf = ConfState.empty⌝ ∨ confStatePts cp dq sm.conf) ∗
      optCell ip sm.index (W64 0) ∗ optCell tp sm.term (W64 0))

/-- A `*Snapshot`'s fields (`full`: the metadata set and full). -/
def snapshotGo (p : Loc) (dq : DFrac) (s : Snapshot) (full : Bool) : IProp GF :=
  iprop(∃ (ds : GoSlice) (mp : Loc), pbRest raftpb.Snapshot p dq ∗
    p.[raftpb.Snapshot, go!"Data"] ↦{dq} ds ∗ ds ↦*□ s.data ∗
    p.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
    if full then snapMetaGo mp dq s.meta true
    else ⌜mp = null ∧ s.meta = Snapshot.empty.meta⌝ ∨ snapMetaGo mp dq s.meta false)

/-- A `*Message`'s fields but `Responses`, its `Entries` slice `es`. -/
def msgCore (p : Loc) (dq : DFrac) (m : Msg) (es : GoSlice) : IProp GF :=
  iprop(∃ (yp tp fp trp ltp ip cp vp sp rp rhp : Loc) (cs : GoSlice),
    pbRest raftpb.Message p dq ∗
    p.[raftpb.Message, go!"Type"] ↦{dq} yp ∗ optCell yp m.type (W32 0) ∗
    p.[raftpb.Message, go!"To"] ↦{dq} tp ∗ optCell tp m.to (W64 0) ∗
    p.[raftpb.Message, go!"From"] ↦{dq} fp ∗ optCell fp m.src (W64 0) ∗
    p.[raftpb.Message, go!"Term"] ↦{dq} trp ∗ optCell trp m.term (W64 0) ∗
    p.[raftpb.Message, go!"LogTerm"] ↦{dq} ltp ∗ optCell ltp m.logTerm (W64 0) ∗
    p.[raftpb.Message, go!"Index"] ↦{dq} ip ∗ optCell ip m.index (W64 0) ∗
    p.[raftpb.Message, go!"Entries"] ↦{dq} es ∗ msgEnts es m ∗
    p.[raftpb.Message, go!"Commit"] ↦{dq} cp ∗ optCell cp m.commit (W64 0) ∗
    p.[raftpb.Message, go!"Vote"] ↦{dq} vp ∗ optCell vp m.vote (W64 0) ∗
    p.[raftpb.Message, go!"Snapshot"] ↦{dq} sp ∗
    (match m.snapshot with
     | none => ⌜sp = null⌝
     | some s => snapshotPts sp DFrac.discard s) ∗
    p.[raftpb.Message, go!"Reject"] ↦{dq} rp ∗ optCell rp m.reject false ∗
    p.[raftpb.Message, go!"RejectHint"] ↦{dq} rhp ∗ optCell rhp m.rejectHint (W64 0) ∗
    p.[raftpb.Message, go!"Context"] ↦{dq} cs ∗ cs ↦*□ m.context)

/-- A `*Message`'s `Responses` field: a slice, read-only for good, of well-formed messages (each
`msgPts` read-only) modelled by `rs`. Only `AsyncStorageWrites`' local messages
(`newStorageAppendMsg`, `newStorageApplyMsg`) carry responses. -/
def msgResps (p : Loc) (dq : DFrac) (rs : List Msg) : IProp GF :=
  iprop(∃ (rsl : GoSlice) (rps : List Loc), p.[raftpb.Message, go!"Responses"] ↦{dq} rsl ∗
    rsl ↦*□ rps ∗ [∗list] q; r ∈ rps; rs, msgPts q DFrac.discard r)

/-- A `*Message`'s fields, its `Entries` slice `es`, no `Responses` (what `msgPts_unfold` and
`msgRecv_unfold` open to). -/
def msgFields (p : Loc) (dq : DFrac) (m : Msg) (es : GoSlice) : IProp GF :=
  iprop(msgCore p dq m es ∗ ∃ rsl : GoSlice, p.[raftpb.Message, go!"Responses"] ↦{dq} rsl ∗
    rsl ↦*□ ([] : List Loc))

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-! ### Persistence, timelessness, non-null -/

def raftpb_persistent.spec : Prop :=
  (∀ p i e, Persistent (entryPts (GF := GF) p DFrac.discard i e)) ∧
  (∀ p hs, Persistent (hardStatePts (GF := GF) p DFrac.discard hs)) ∧
  (∀ p cs, Persistent (confStatePts (GF := GF) p DFrac.discard cs)) ∧
  (∀ p cs, Persistent (confStateFull (GF := GF) p DFrac.discard cs)) ∧
  (∀ p s, Persistent (snapshotPts (GF := GF) p DFrac.discard s)) ∧
  (∀ p s, Persistent (snapshotRaw (GF := GF) p DFrac.discard s)) ∧
  (∀ p m, Persistent (msgPts (GF := GF) p DFrac.discard m)) ∧
  (∀ p m rs, Persistent (msgOut (GF := GF) p DFrac.discard m rs)) ∧
  (∀ p c, Persistent (confChangeV1Pts (GF := GF) p DFrac.discard c)) ∧
  (∀ p c, Persistent (confChangeV2Pts (GF := GF) p DFrac.discard c)) ∧
  (∀ p s, Persistent (singlePts (GF := GF) p DFrac.discard s)) ∧
  (∀ t p, Persistent (pbRest (GF := GF) t p DFrac.discard))

/-- Every predicate is timeless (a client keeps them in invariants: R1's `memStor`). -/
def raftpb_timeless.spec : Prop :=
  (∀ p dq i e, Timeless (entryPts (GF := GF) p dq i e)) ∧
  (∀ p dq hs, Timeless (hardStatePts (GF := GF) p dq hs)) ∧
  (∀ p dq cs, Timeless (confStatePts (GF := GF) p dq cs)) ∧
  (∀ p dq cs, Timeless (confStateFull (GF := GF) p dq cs)) ∧
  (∀ p dq s, Timeless (snapshotPts (GF := GF) p dq s)) ∧
  (∀ p dq s, Timeless (snapshotRaw (GF := GF) p dq s)) ∧
  (∀ p dq m, Timeless (msgPts (GF := GF) p dq m)) ∧
  (∀ p m, Timeless (msgRecv (GF := GF) p m)) ∧
  (∀ p dq m rs, Timeless (msgOut (GF := GF) p dq m rs)) ∧
  (∀ p dq c, Timeless (confChangeV1Pts (GF := GF) p dq c)) ∧
  (∀ p dq c, Timeless (confChangeV2Pts (GF := GF) p dq c)) ∧
  (∀ p dq s, Timeless (singlePts (GF := GF) p dq s)) ∧
  (∀ t p dq, Timeless (pbRest (GF := GF) t p dq))

/-- Every predicate is at a non-`nil` pointer (R2's `ReqApplyConf`: `confStatePts ⊢ p ≠ null`). -/
def raftpb_ne_null.spec : Prop :=
  (∀ p dq i e, entryPts (GF := GF) p dq i e ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq hs, hardStatePts (GF := GF) p dq hs ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq cs, confStatePts (GF := GF) p dq cs ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq cs, confStateFull (GF := GF) p dq cs ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq s, snapshotPts (GF := GF) p dq s ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq s, snapshotRaw (GF := GF) p dq s ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m, msgPts (GF := GF) p dq m ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m rs, msgOut (GF := GF) p dq m rs ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq c, confChangeV1Pts (GF := GF) p dq c ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq c, confChangeV2Pts (GF := GF) p dq c ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq s, singlePts (GF := GF) p dq s ⊢ ⌜p ≠ null⌝)

/-- **Fractions**: an owned message may be made read-only for good (R1: `Ready`'s snapshot, R2:
a sent message, R3: the log's entries), and two holdings of one message agree. -/
def raftpb_persist.spec : Prop :=
  (∀ p i e, entryPts (GF := GF) p (DFrac.own 1) i e ⊢ |==> entryPts p DFrac.discard i e) ∧
  (∀ p hs, hardStatePts (GF := GF) p (DFrac.own 1) hs ⊢ |==> hardStatePts p DFrac.discard hs) ∧
  (∀ p cs, confStatePts (GF := GF) p (DFrac.own 1) cs ⊢ |==> confStatePts p DFrac.discard cs) ∧
  (∀ p cs, confStateFull (GF := GF) p (DFrac.own 1) cs ⊢ |==> confStateFull p DFrac.discard cs) ∧
  (∀ p s, snapshotPts (GF := GF) p (DFrac.own 1) s ⊢ |==> snapshotPts p DFrac.discard s) ∧
  (∀ p m, msgPts (GF := GF) p (DFrac.own 1) m ⊢ |==> msgPts p DFrac.discard m) ∧
  (∀ p c, confChangeV1Pts (GF := GF) p (DFrac.own 1) c ⊢ |==> confChangeV1Pts p DFrac.discard c) ∧
  (∀ p c, confChangeV2Pts (GF := GF) p (DFrac.own 1) c ⊢ |==> confChangeV2Pts p DFrac.discard c) ∧
  (∀ p dq dq' m m', msgPts (GF := GF) p dq m ∗ msgPts p dq' m' ⊢ ⌜m = m'⌝) ∧
  (∀ p dq dq' s s', snapshotPts (GF := GF) p dq s ∗ snapshotPts p dq' s' ⊢ ⌜s = s'⌝)

/-- A fresh message's bookkeeping (zero `state`, `sizeCache`, `unknownFields`: a composite literal
`&pb.T{...}` or `new(pb.T)`) is its `pbRest`. -/
def pbRest_zero.spec : Prop := ∀ (t : Type) (p : Loc),
  p.[t, go!"state"] ↦ (zero_val google_golang_org.protobuf.internal.impl.MessageState) ∗
    p.[t, go!"sizeCache"] ↦ (W32 0) ∗ p.[t, go!"unknownFields"] ↦ slice.nil ⊢
  pbRest (GF := GF) t p (DFrac.own 1)

/-! ### Unfold laws: the Go fields

Each predicate is exactly its fields (both directions: a client reads them, and at `own 1` writes a
field and folds the predicate back at the new model). -/

def entryPts_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (i : w64) (e : LogEntry),
  entryPts (GF := GF) p dq i e ⊣⊢
    ∃ (tp ip yp : Loc) (ds : GoSlice), pbRest raftpb.Entry p dq ∗
    p.[raftpb.Entry, go!"Term"] ↦{dq} tp ∗ optCell tp e.term (W64 0) ∗
    p.[raftpb.Entry, go!"Index"] ↦{dq} ip ∗ optCell ip i (W64 0) ∗
    p.[raftpb.Entry, go!"Type"] ↦{dq} yp ∗ optCell yp e.type (W32 0) ∗
    p.[raftpb.Entry, go!"Data"] ↦{dq} ds ∗ ds ↦*□ e.data

def hardStatePts_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (hs : HardState),
  hardStatePts (GF := GF) p dq hs ⊣⊢
    ∃ (tp vp cp : Loc), pbRest raftpb.HardState p dq ∗
    p.[raftpb.HardState, go!"Term"] ↦{dq} tp ∗ optCell tp hs.term (W64 0) ∗
    p.[raftpb.HardState, go!"Vote"] ↦{dq} vp ∗ optCell vp hs.vote (W64 0) ∗
    p.[raftpb.HardState, go!"Commit"] ↦{dq} cp ∗ optCell cp hs.commit (W64 0)

def confStatePts_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (cs : ConfState),
  confStatePts (GF := GF) p dq cs ⊣⊢ confStateGo p dq cs false

def confStateFull_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (cs : ConfState),
  confStateFull (GF := GF) p dq cs ⊣⊢ confStateGo p dq cs true

def snapshotPts_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (s : Snapshot),
  snapshotPts (GF := GF) p dq s ⊣⊢ snapshotGo p dq s true

def snapshotRaw_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (s : Snapshot),
  snapshotRaw (GF := GF) p dq s ⊣⊢ snapshotGo p dq s false

/-- **A message's fields.** Its entries and snapshot read-only for good; a `MsgApp`'s entries at
`Index + 1, Index + 2, ...` (R3's `maybeAppend`: `entriesRO sl (m.index + 1) m.entries`), any other
type's at any index; `Responses` empty. No capacity of the `Entries` slice is owned (a `MsgApp`'s
entries are the leader's log's, shared read-only; a received message's capacity: `msgRecv`). -/
def msgPts_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : Msg),
  msgPts (GF := GF) p dq m ⊣⊢ ∃ es : GoSlice, msgFields p dq m es

/-- **A received message** (`msgRecv`): its fields at `own 1`, and the spare capacity of its
`Entries` slice owned (raft's `unstable` may adopt the slice and append into it). -/
def msgRecv_unfold.spec : Prop := ∀ (p : Loc) (m : Msg),
  msgRecv (GF := GF) p m ⊣⊢ ∃ es : GoSlice, msgFields p (DFrac.own 1) m es ∗
    ownSliceCap Loc es (DFrac.own 1)

/-- **A local message with responses** (`msgOut`): `msgPts`'s fields but `Responses`, which holds
the responses. Read and written as `msgPts` is (`newStorageAppendMsg` builds the message, then sets
`Responses`). -/
def msgOut_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : Msg) (rs : List Msg),
  msgOut (GF := GF) p dq m rs ⊣⊢ ∃ es : GoSlice, msgCore p dq m es ∗ msgResps p dq rs

/-- **No response: a well-formed message.** -/
def msgOut_nil.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : Msg),
  msgOut (GF := GF) p dq m [] ⊣⊢ msgPts p dq m

/-- **A received message from a fresh protobuf message** (verify round, A5-completeness F4: the
introduction of `msgRecv`, coordinator decision A12): a `*Message` that is a merge destination
(`Proto.mergeDst`: owned, its repeated fields' slices to their capacity, its set submessages
writable: what protobuf's `Clone` and `Unmarshal` allocate) holding a well-formed content of model
`m` is a received message (its snapshot and entries made read-only for good, the `Entries`
capacity kept). Second pass: 2a's `Clone.spec` gives `mergeDst t p' (norm c)` of a `msgPts`'s
content `c` (`raftpb_norm` carries `msgIs` over), `Unmarshal.spec` a canonical `mergeDst t p c` with
`encodes t c bs` (`msgEncodes bs m`, `encodes_fun` and `raftpb_norm` give `msgIs c m`). -/
def msgRecv_intro.spec : Prop := ∀ (p : Loc) (c : Proto.Content) (m : Msg),
  Proto.mergeDst (GF := GF) raftpb.Message.ty p c ∗ ⌜msgIs c m⌝ ⊢ |==> msgRecv p m

/-- **A received message lends a read share of itself** (rafthttp's request at the verify round):
`msgPts` at some fraction (the getters work at any), returned to rebuild `msgRecv`. Not at `own 1`:
the kept share pins the `Entries` slice whose capacity `msgRecv` owns (a full `msgPts` could come
back with another slice). -/
def msgRecv_lend.spec : Prop := ∀ (p : Loc) (m : Msg),
  msgRecv (GF := GF) p m ⊢ ∃ dq : DFrac, msgPts p dq m ∗ (msgPts p dq m -∗ msgRecv p m)

def confChangeV1Pts_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (c : ConfChangeV1),
  confChangeV1Pts (GF := GF) p dq c ⊣⊢
    ∃ (yp np ip : Loc) (cs : GoSlice), pbRest raftpb.ConfChange p dq ∗
    p.[raftpb.ConfChange, go!"Type"] ↦{dq} yp ∗ optCell yp c.type (W32 0) ∗
    p.[raftpb.ConfChange, go!"NodeId"] ↦{dq} np ∗ optCell np c.nodeId (W64 0) ∗
    p.[raftpb.ConfChange, go!"Context"] ↦{dq} cs ∗ cs ↦*□ c.context ∗
    p.[raftpb.ConfChange, go!"Id"] ↦{dq} ip ∗ optCell ip c.id (W64 0)

/-- A `ConfChangeV2`'s fields: its `Changes` slice and singles at `dq` (R4: `ccsPts` of the field,
which `raft.applyConfChange` passes as `cc.Changes...`). -/
def confChangeV2Pts_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (c : ConfChangeV2),
  confChangeV2Pts (GF := GF) p dq c ⊣⊢
    ∃ (tp : Loc) (chs cs : GoSlice), pbRest raftpb.ConfChangeV2 p dq ∗
    p.[raftpb.ConfChangeV2, go!"Transition"] ↦{dq} tp ∗ optCell tp c.transition (W32 0) ∗
    p.[raftpb.ConfChangeV2, go!"Changes"] ↦{dq} chs ∗ ccsPts chs dq c.changes ∗
    p.[raftpb.ConfChangeV2, go!"Context"] ↦{dq} cs ∗ cs ↦*□ c.context

def singlePts_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (s : ConfChangeSingle),
  singlePts (GF := GF) p dq s ⊣⊢
    ∃ (yp np : Loc), pbRest raftpb.ConfChangeSingle p dq ∗
    p.[raftpb.ConfChangeSingle, go!"Type"] ↦{dq} yp ∗ optCell yp s.type (W32 0) ∗
    p.[raftpb.ConfChangeSingle, go!"NodeId"] ↦{dq} np ∗ optCell np s.nodeId (W64 0)

/-! ### Relation laws: the content `Proto.msgAt` holds

What protobuf's specs (2a: `Clone`, `Marshal`, `Unmarshal`, `Size`, `Equal`) are stated over. A
clone holds the same content, so the same model (and the same fullness); a decoded message holds the
content the bytes encode (`Proto.encodes_fun`), so the sender's model and facts. -/

def entryPts_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (i : w64) (e : LogEntry),
  entryPts (GF := GF) p dq i e ⊣⊢ ∃ c, Proto.msgAt raftpb.Entry.ty p dq c ∗ ⌜entryIs c i e⌝

def hardStatePts_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (hs : HardState),
  hardStatePts (GF := GF) p dq hs ⊣⊢ ∃ c, Proto.msgAt raftpb.HardState.ty p dq c ∗ ⌜hardStateIs c hs⌝

def confStatePts_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (cs : ConfState),
  confStatePts (GF := GF) p dq cs ⊣⊢
    ∃ c, Proto.msgAt raftpb.ConfState.ty p dq c ∗ ⌜confStateIs c cs false⌝

def confStateFull_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (cs : ConfState),
  confStateFull (GF := GF) p dq cs ⊣⊢
    ∃ c, Proto.msgAt raftpb.ConfState.ty p dq c ∗ ⌜confStateIs c cs true⌝

def snapshotPts_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (s : Snapshot),
  snapshotPts (GF := GF) p dq s ⊣⊢
    ∃ c, Proto.msgAt raftpb.Snapshot.ty p dq c ∗ ⌜snapshotIs c s true⌝

def snapshotRaw_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (s : Snapshot),
  snapshotRaw (GF := GF) p dq s ⊣⊢
    ∃ c, Proto.msgAt raftpb.Snapshot.ty p dq c ∗ ⌜snapshotIs c s false⌝

def msgPts_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : Msg),
  msgPts (GF := GF) p dq m ⊣⊢ ∃ c, Proto.msgAt raftpb.Message.ty p dq c ∗ ⌜msgIs c m⌝

def confChangeV1Pts_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (cc : ConfChangeV1),
  confChangeV1Pts (GF := GF) p dq cc ⊣⊢
    ∃ c, Proto.msgAt raftpb.ConfChange.ty p dq c ∗ ⌜confChangeV1Is c cc⌝

def confChangeV2Pts_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (cc : ConfChangeV2),
  confChangeV2Pts (GF := GF) p dq cc ⊣⊢
    ∃ c, Proto.msgAt raftpb.ConfChangeV2.ty p dq c ∗ ⌜confChangeV2Is c cc⌝

def singlePts_msgAt.spec : Prop := ∀ (p : Loc) (dq : DFrac) (s : ConfChangeSingle),
  singlePts (GF := GF) p dq s ⊣⊢
    ∃ c, Proto.msgAt raftpb.ConfChangeSingle.ty p dq c ∗ ⌜singleIs c s⌝

/-- **A `MsgApp`'s entries are the log's from `Index + 1`** (R3's `raftLog.maybeAppend`). -/
def msgEnts_app.spec : Prop := ∀ (sl : GoSlice) (m : Msg), m.type = MsgApp →
  msgEnts (GF := GF) sl m ⊢ entriesRO sl (uint.nat m.index + 1) m.entries

/-! ### Content laws -/

/-- **A plain full `ConfState`'s wire view is its model** (`proto.Equal` of two such contents with
one model answers `true`: `Equivalent`). Up to `Proto.norm` (second pass: a content holds Go values,
so a `nil` and an empty list differ as contents, not on the wire). -/
def confState_ext.spec : Prop := ∀ (c c' : Proto.Content) (cs : ConfState),
  confStateIs c cs true → confStateIs c' cs true → Proto.norm c = Proto.norm c'

/-- **raftpb's models survive the wire view** (second pass, after 2a made `Content` hold Go values
with the wire view `Proto.norm`): each relation of a content to its model holds of `norm c` too.
What it needs of `norm`: raftpb is proto2, so every optional scalar and submessage field has
explicit presence (a pointer: `nil` is unset, a set zero is populated), which `norm` keeps; it only
replaces an empty repeated field or empty `bytes` by `nil`, which the models do not distinguish
(`List`s), and keeps plainness, depth, size and `marshalOk` (`Proto.norm_facts`). Used across
`Clone` (the copy holds `norm c`), `Unmarshal` (a decoded content is canonical: with
`encodes_fun` the decoded content is `norm` of the sender's) and `msgRecv_intro`. -/
def raftpb_norm.spec : Prop := ∀ (c : Proto.Content),
  (∀ i e, entryIs c i e → entryIs (Proto.norm c) i e) ∧
  (∀ hs, hardStateIs c hs → hardStateIs (Proto.norm c) hs) ∧
  (∀ cs full, confStateIs c cs full → confStateIs (Proto.norm c) cs full) ∧
  (∀ s full, snapshotIs c s full → snapshotIs (Proto.norm c) s full) ∧
  (∀ m, msgIs c m → msgIs (Proto.norm c) m) ∧
  (∀ cc, confChangeV1Is c cc → confChangeV1Is (Proto.norm c) cc) ∧
  (∀ cc, confChangeV2Is c cc → confChangeV2Is (Proto.norm c) cc) ∧
  (∀ sc, singleIs c sc → singleIs (Proto.norm c) sc)

/-- **raftpb's message types have no floating-point field** (`proto.Equal`'s converse,
`Equal.spec`'s `noFloats t → norm c = norm d → b = true`: `Equivalent` needs it for `ConfState`). -/
def noFloats_raftpb.spec : Prop :=
  Proto.noFloats raftpb.Entry.ty ∧ Proto.noFloats raftpb.HardState.ty ∧
  Proto.noFloats raftpb.ConfState.ty ∧ Proto.noFloats raftpb.SnapshotMetadata.ty ∧
  Proto.noFloats raftpb.Snapshot.ty ∧ Proto.noFloats raftpb.Message.ty ∧
  Proto.noFloats raftpb.ConfChange.ty ∧ Proto.noFloats raftpb.ConfChangeV2.ty ∧
  Proto.noFloats raftpb.ConfChangeSingle.ty

/-- **The bootstrap `ConfChange` literal** `&pb.ConfChange{Type: AddNode.Enum(), NodeId: new(id),
Context: ctx}` (`RawNode.Bootstrap`, `bootstrap.go:52`), with a non-empty context, holds the
bootstrap content. -/
def bootCC_lit.spec : Prop := ∀ (p yp np : Loc) (cs : GoSlice) (id : w64) (ctx : List w8),
  ctx ≠ [] →
  pbRest (GF := GF) raftpb.ConfChange p (DFrac.own 1) ∗
    p.[raftpb.ConfChange, go!"Type"] ↦ yp ∗ yp ↦□ ConfChangeAddNode ∗
    p.[raftpb.ConfChange, go!"NodeId"] ↦ np ∗ np ↦□ id ∗
    p.[raftpb.ConfChange, go!"Context"] ↦ cs ∗ cs ↦*□ ctx ∗
    p.[raftpb.ConfChange, go!"Id"] ↦ (null : Loc) ⊢
  ∃ c, Proto.msgAt raftpb.ConfChange.ty p (DFrac.own 1) c ∗ ⌜bootCC id ctx c⌝

/-- **The bootstrap content**: unique, the model `⟨AddNode, id, ctx, 0⟩`, encoded by
`bootEntryData id ctx`, and canonical (`norm c = c`: its set fields are populated, `Id` is unset and
the context non-empty; second pass) (so `decodeConfChange EntryConfChange (bootEntryData id ctx) = some (.v1
⟨AddNode, id, ctx, 0⟩)`: R1's `bootEntryData_decode`). -/
def bootCC_facts.spec : Prop := ∀ (id : w64) (ctx : List w8) (c c' : Proto.Content),
  bootCC id ctx c →
    (bootCC id ctx c' → c = c') ∧
    confChangeV1Is c ⟨ConfChangeAddNode, id, ctx, W64 0⟩ ∧
    Proto.encodes raftpb.ConfChange.ty c (bootEntryData id ctx) ∧
    Proto.norm c = c

/-- **raftpb's message types have no map field** (`raft.proto`: scalars, bytes, enums, repeated
scalars and submessages only): `proto.Marshal` of each is a function of the content (2a's
`Marshal.spec`: `noMaps t → bs = marshalOut t c`). -/
def noMaps_raftpb.spec : Prop :=
  Proto.noMaps raftpb.Entry.ty ∧ Proto.noMaps raftpb.HardState.ty ∧
  Proto.noMaps raftpb.ConfState.ty ∧ Proto.noMaps raftpb.SnapshotMetadata.ty ∧
  Proto.noMaps raftpb.Snapshot.ty ∧ Proto.noMaps raftpb.Message.ty ∧
  Proto.noMaps raftpb.ConfChange.ty ∧ Proto.noMaps raftpb.ConfChangeV2.ty ∧
  Proto.noMaps raftpb.ConfChangeSingle.ty

/-- **The bootstrap bytes are what `proto.Marshal` gives the bootstrap change** (verify round,
A5 F4/F3: every founder appends the same bytes): for the content `c` of the bootstrap `ConfChange`
(`bootCC id ctx c`, unique by `bootCC_facts`), `bootEntryData id ctx` is `Marshal`'s output.
`RawNode.Bootstrap` (R1) gets its bytes from `Marshal.spec`'s `noMaps t → bs = marshalOut t c`
with `noMaps_raftpb`. Intended realization: `bootEntryData id ctx` is defined as `marshalOut
ConfChange.ty` of the unique `bootCC id ctx` content. -/
def bootEntryData_marshal.spec : Prop := ∀ (id : w64) (ctx : List w8) (c : Proto.Content),
  bootCC id ctx c → bootEntryData id ctx = Proto.marshalOut raftpb.ConfChange.ty c

/-- **The empty bytes decode to the empty `ConfChangeV2`** (the auto-leave entry raft appends with
`MarshalConfChange(nil)`'s `nil` data). -/
def decodeConfChange_empty.spec : Prop :=
  decodeConfChange EntryConfChangeV2 [] = some (.v2 ⟨ConfChangeTransitionAuto, [], []⟩)

/-- **Decoding is a function of the bytes** (from `Proto.encodes_fun`, up to `norm`, and
`raftpb_norm`: the models are functions of the wire view). -/
def wire_fun.spec : Prop :=
  (∀ bs (m m' : Msg), msgEncodes bs m → msgEncodes bs m' → m = m') ∧
  (∀ bs (i i' : w64) (e e' : LogEntry), entryEncodes bs i e → entryEncodes bs i' e' →
    i = i' ∧ e = e')

end laws

end RaftPb
end EtcdGrove
end Perennial
