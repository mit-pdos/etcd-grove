/-
**raftpb's `Entry` and `ConfChangeV2` on the wire** (protobuf trust-boundary stage S1,
mit-pdos/etcd-grove#37): protobuf-go v1.36.12's `proto.Marshal` of an `Entry` and `proto.Unmarshal`
of an `Entry` and of a `ConfChangeV2`, as functions of plain values over the generic wire format
(`Proof/google_golang_org/protobuf/proto/Wire.lean`) at the types' schemas (`PbSchema.lean`).
Pure and computable (no Goose type): `entryEncC`, `entDecode` (`PbEntryTypeCore.lean`) and
`ccDecodeV2` (`CCModel.lean`) are these at the model records, and the vectors module
`Proof/google_golang_org/protobuf/proto/EntryWireVectors.lean` checks these against protobuf-go.

`raft.proto` (proto2) at the pin: `Entry` is `Type` 1 (enum), `Term` 2, `Index` 3 (`uint64`),
`Data` 4 (`bytes`), each `optional`; `ConfChangeV2` is `transition` 1 (enum), `changes` 2
(repeated `ConfChangeSingle`), `context` 3 (`bytes`); `ConfChangeSingle` is `type` 1 (enum),
`node_id` 2 (`uint64`). An enum is an `int32`: written as its 64-bit sign extension
(`appendInt32Ptr`, the enum pointer coder being the `int32` one), read as the low 32 bits of the
varint (`int32(v)`: protobuf-go treats every enum as open). A scalar's last record wins; a
`bytes` field's last record wins (an empty one reads as the empty bytes, as a nil one does through
the getter); each `changes` record appends a change decoded from its bytes, and a change that does
not decode fails the whole message.
-/
module

public import Proof.google_golang_org.protobuf.proto.Wire
public import Proof.google_golang_org.protobuf.proto.PbSchema

@[expose] public section

namespace Perennial
namespace EtcdGrove

open Wire

/-! ## `Entry` -/

/-- An enum's varint: the `int32`, sign-extended to 64 bits. -/
def enumVarint (t : w32) : Nat := (BitVec.ofInt 64 t.toInt).toNat

/-- An entry's records, in field-number order (`Type`, `Term`, `Index`, `Data`), each iff present. -/
def entryRecs (type : Option w32) (term index : Option w64) (data : Option (List w8)) :
    List (Nat × FVal) :=
  optF 1 (fun t => .varint (enumVarint t)) type ++ optF 2 (fun v => .varint v.toNat) term ++
    optF 3 (fun v => .varint v.toNat) index ++ optF 4 .len data

/-- **`proto.Marshal` of an `Entry`** of these fields' presence and values and these unknown
fields. -/
def entryEncRaw (type : Option w32) (term index : Option w64) (data : Option (List w8))
    (uf : List w8) : List w8 :=
  encode (entryRecs type term index data) uf

/-- **`proto.Unmarshal` into an `Entry`**: what `GetTerm()`, `GetIndex()`, `GetType()`, `GetData()`
then return, or `none` where it returns an error. -/
def entDecodeRaw (bs : List w8) : Option (w64 × w64 × w32 × List w8) :=
  (decode entrySchema bs).map fun p =>
    (BitVec.ofNat 64 ((lastVarint p.1 2).getD 0), BitVec.ofNat 64 ((lastVarint p.1 3).getD 0),
      BitVec.ofNat 32 ((lastVarint p.1 1).getD 0), (lastLen p.1 4).getD [])

theorem enumVarint_lt (t : w32) : enumVarint t < 2 ^ 64 := (BitVec.ofInt 64 t.toInt).isLt

theorem ofNat_enumVarint (t : w32) : BitVec.ofNat 32 (enumVarint t) = t := by
  unfold enumVarint
  rw [BitVec.ofNat_toNat]
  show (t.signExtend 64).setWidth 32 = t
  bv_decide

theorem entryRecs_ok (type : Option w32) (term index : Option w64) (data : Option (List w8))
    (hd : ∀ d, data = some d → d.length < 2 ^ 64) :
    ∀ p ∈ entryRecs type term index data, RecOk entrySchema p := by
  intro p hp
  simp only [entryRecs, optF, List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · cases type <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, enumVarint_lt _⟩
  · cases term <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases index <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases h : data <;> simp [h] at hp; subst hp
    exact ⟨by simp, by simp, rfl, hd _ h⟩

/-- **The entry round trip**: `Unmarshal(Marshal(e))` reads the fields as set (an absent one as
zero), for unknown fields as the decoder leaves them. -/
theorem entDecodeRaw_enc (type : Option w32) (term index : Option w64) (data : Option (List w8))
    (uf : List w8) (hu : ufWire entrySchema uf) (hd : ∀ d, data = some d → d.length < 2 ^ 64) :
    entDecodeRaw (entryEncRaw type term index data uf) =
      some (term.getD 0, index.getD 0, type.getD 0, data.getD []) := by
  unfold entDecodeRaw entryEncRaw
  rw [decode_encode (entryRecs_ok type term index data hd) hu]
  cases type <;> cases term <;> cases index <;> cases data <;>
    simp [entryRecs, optF, lastVarint, lastLen, ofNat_enumVarint]

theorem entryRecs_length (type : Option w32) (term index : Option w64) (data : Option (List w8)) :
    (encFields (entryRecs type term index data)).length =
      (match type with | none => 0 | some t => 1 + varintSize (enumVarint t)) +
      (match term with | none => 0 | some v => 1 + varintSize v.toNat) +
      (match index with | none => 0 | some v => 1 + varintSize v.toNat) +
      (match data with | none => 0 | some bs => 1 + varintSize bs.length + bs.length) := by
  simp only [entryRecs, encFields_append]
  cases type <;> cases term <;> cases index <;> cases data <;>
    simp [optF, encFields, record, tag, varintEnc_lt128, FVal.wt, FVal.payload, varintSize] <;> omega

/-! ## `ConfChangeV2` -/

/-- **`proto.Unmarshal` into a `ConfChangeSingle`**: `GetType()`, `GetNodeId()`. -/
def ccsDecodeRaw (bs : List w8) : Option (w32 × w64) :=
  (decode ccsSchema bs).map fun p =>
    (BitVec.ofNat 32 ((lastVarint p.1 1).getD 0), BitVec.ofNat 64 ((lastVarint p.1 2).getD 0))

/-- **`proto.Unmarshal` into a `ConfChangeV2`**: `GetTransition()`, the changes' getters,
`GetContext()`; `none` where it returns an error. -/
def cc2DecodeRaw (bs : List w8) : Option (w32 × List (w32 × w64) × List w8) :=
  match decode cc2Schema bs with
  | none => none
  | some p =>
    match (allLen p.1 2).mapM ccsDecodeRaw with
    | none => none
    | some chs => some (BitVec.ofNat 32 ((lastVarint p.1 1).getD 0), chs, (lastLen p.1 3).getD [])

theorem cc2DecodeRaw_nil : cc2DecodeRaw [] = some (0, [], []) := by
  simp [cc2DecodeRaw, decode_nil, allLen, lastVarint, lastLen]

/-! ## `ConfChange` (2026-11-24, the trace check's bootstrap log)

The legacy conf change, `raft.proto`'s `ConfChange` (proto2): `id` 1 (`uint64`), `type` 2 (enum),
`node_id` 3 (`uint64`), `context` 4 (`bytes`), each `optional`; declared in the order `type`,
`node_id`, `context`, `id`, but protobuf-go writes the fields in field-number order. `ccDecodeV1`
(`CCModel.lean`) is `cc1DecodeRaw` at the model record (until 2026-11-24 opaque); the vectors module
`Proof/google_golang_org/protobuf/proto/ConfChangeWireVectors.lean` checks both functions below
against protobuf-go. -/

/-- A `ConfChange`'s records, in field-number order (`id`, `type`, `node_id`, `context`), each iff
present. -/
def cc1Recs (id : Option w64) (type : Option w32) (nodeId : Option w64) (ctx : Option (List w8)) :
    List (Nat × FVal) :=
  optF 1 (fun v => .varint v.toNat) id ++ optF 2 (fun t => .varint (enumVarint t)) type ++
    optF 3 (fun v => .varint v.toNat) nodeId ++ optF 4 .len ctx

/-- **`proto.Marshal` of a `ConfChange`** of these fields' presence and values and these unknown
fields. -/
def cc1EncRaw (id : Option w64) (type : Option w32) (nodeId : Option w64) (ctx : Option (List w8))
    (uf : List w8) : List w8 :=
  encode (cc1Recs id type nodeId ctx) uf

/-- **`proto.Unmarshal` into a `ConfChange`**: what `GetId()`, `GetType()`, `GetNodeId()`,
`GetContext()` then return, or `none` where it returns an error. -/
def cc1DecodeRaw (bs : List w8) : Option (w64 × w32 × w64 × List w8) :=
  (decode ccSchema bs).map fun p =>
    (BitVec.ofNat 64 ((lastVarint p.1 1).getD 0), BitVec.ofNat 32 ((lastVarint p.1 2).getD 0),
      BitVec.ofNat 64 ((lastVarint p.1 3).getD 0), (lastLen p.1 4).getD [])

theorem cc1Recs_ok (id : Option w64) (type : Option w32) (nodeId : Option w64)
    (ctx : Option (List w8)) (hc : ∀ c, ctx = some c → c.length < 2 ^ 64) :
    ∀ p ∈ cc1Recs id type nodeId ctx, RecOk ccSchema p := by
  intro p hp
  simp only [cc1Recs, optF, List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · cases id <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases type <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, enumVarint_lt _⟩
  · cases nodeId <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases h : ctx <;> simp [h] at hp; subst hp
    exact ⟨by simp, by simp, rfl, hc _ h⟩

/-- **The `ConfChange` round trip**: `Unmarshal(Marshal(cc))` reads the fields as set (an absent
one as zero, an absent context as the empty bytes), for unknown fields as the decoder leaves them. -/
theorem cc1DecodeRaw_enc (id : Option w64) (type : Option w32) (nodeId : Option w64)
    (ctx : Option (List w8)) (uf : List w8) (hu : ufWire ccSchema uf)
    (hc : ∀ c, ctx = some c → c.length < 2 ^ 64) :
    cc1DecodeRaw (cc1EncRaw id type nodeId ctx uf) =
      some (id.getD 0, type.getD 0, nodeId.getD 0, ctx.getD []) := by
  unfold cc1DecodeRaw cc1EncRaw
  rw [decode_encode (cc1Recs_ok id type nodeId ctx hc) hu]
  cases id <;> cases type <;> cases nodeId <;> cases ctx <;>
    simp [cc1Recs, optF, lastVarint, lastLen, ofNat_enumVarint]


/-! ## Repeated scalars and merged sub-messages -/

/-- A packed record's varints (`consumeUint64Slice`'s loop): every value, or `none` if one does not
parse. `fuel` above the input's length never runs out. -/
def packedVarints : Nat → List w8 → Option (List Nat)
  | 0, _ => none
  | fuel + 1, bs =>
    if bs = [] then some []
    else match readVarint bs with
      | none => none
      | some (v, r) => (packedVarints fuel r).map (v :: ·)

/-- **A repeated `uint64` field's values** (proto2 unpacked, but the decoder takes both forms): each
varint record one value, each length-delimited record its packed varints, in input order; `none`
if a packed record does not parse (`errDecode`). -/
def repVarint (ks : List (Nat × FVal)) (num : Nat) : Option (List Nat) :=
  ((ks.filterMap fun (p : Nat × FVal) => if p.1 = num then some p.2 else none).mapM fun (v : FVal) =>
    match v with
    | .varint n => some [n]
    | .len bs => packedVarints (bs.length + 1) bs
    | _ => some []).map List.flatten

/-- A `bool` field's value (`protowire.DecodeBool`: non-zero is `true`). -/
def lastBool (ks : List (Nat × FVal)) (num : Nat) : Bool :=
  (lastVarint ks num).getD 0 != 0

/-! ## `Message` and its sub-messages: the encoding

Each takes its sub-messages already encoded (a nested message is written as a length-delimited
record of its own encoding, `appendMessageInfo`). -/

/-- A `bool`'s varint. -/
def boolVarint (b : Bool) : Nat := if b then 1 else 0

/-- A `ConfState`'s records: the four unpacked repeated `uint64`s, then `auto_leave`. -/
def csRecs (voters learners votersOutgoing learnersNext : List w64) (autoLeave : Option Bool) :
    List (Nat × FVal) :=
  voters.map (fun v => (1, .varint v.toNat)) ++ learners.map (fun v => (2, .varint v.toNat)) ++
    votersOutgoing.map (fun v => (3, .varint v.toNat)) ++
    learnersNext.map (fun v => (4, .varint v.toNat)) ++ optF 5 (fun b => .varint (boolVarint b)) autoLeave

/-- **`proto.Marshal` of a `ConfState`.** -/
def csEncRaw (voters learners votersOutgoing learnersNext : List w64) (autoLeave : Option Bool)
    (uf : List w8) : List w8 :=
  encode (csRecs voters learners votersOutgoing learnersNext autoLeave) uf

/-- A `SnapshotMetadata`'s records (`conf_state` encoded). -/
def metaRecs (cs : Option (List w8)) (index term : Option w64) : List (Nat × FVal) :=
  optF 1 .len cs ++ optF 2 (fun v => .varint v.toNat) index ++ optF 3 (fun v => .varint v.toNat) term

/-- **`proto.Marshal` of a `SnapshotMetadata`**, its `conf_state` encoded. -/
def metaEncRaw (cs : Option (List w8)) (index term : Option w64) (uf : List w8) : List w8 :=
  encode (metaRecs cs index term) uf

/-- A `Snapshot`'s records (`metadata` encoded). -/
def snapRecs (data md : Option (List w8)) : List (Nat × FVal) :=
  optF 1 .len data ++ optF 2 .len md

/-- **`proto.Marshal` of a `Snapshot`**, its `metadata` encoded. -/
def snapEncRaw (data md : Option (List w8)) (uf : List w8) : List w8 :=
  encode (snapRecs data md) uf

/-- A `Message`'s records, in field-number order (`type` 1, `to` 2, `from` 3, `term` 4, `logTerm`
5, `index` 6, `entries` 7, `commit` 8, `snapshot` 9, `reject` 10, `rejectHint` 11, `context` 12,
`vote` 13, `responses` 14), its entries, snapshot and responses encoded. -/
def msgRecs (type : Option w32) (to frm term logTerm index : Option w64) (ents : List (List w8))
    (commit : Option w64) (snap : Option (List w8)) (reject : Option Bool) (rejectHint : Option w64)
    (ctx : Option (List w8)) (vote : Option w64) (resps : List (List w8)) : List (Nat × FVal) :=
  optF 1 (fun t => .varint (enumVarint t)) type ++ optF 2 (fun v => .varint v.toNat) to ++
    optF 3 (fun v => .varint v.toNat) frm ++ optF 4 (fun v => .varint v.toNat) term ++
    optF 5 (fun v => .varint v.toNat) logTerm ++ optF 6 (fun v => .varint v.toNat) index ++
    ents.map (fun e => (7, .len e)) ++ optF 8 (fun v => .varint v.toNat) commit ++
    optF 9 .len snap ++ optF 10 (fun b => .varint (boolVarint b)) reject ++
    optF 11 (fun v => .varint v.toNat) rejectHint ++ optF 12 .len ctx ++
    optF 13 (fun v => .varint v.toNat) vote ++ resps.map (fun r => (14, .len r))

/-- **`proto.Marshal` of a `Message`**, its entries, snapshot and responses encoded. -/
def msgEncRaw (type : Option w32) (to frm term logTerm index : Option w64) (ents : List (List w8))
    (commit : Option w64) (snap : Option (List w8)) (reject : Option Bool) (rejectHint : Option w64)
    (ctx : Option (List w8)) (vote : Option w64) (resps : List (List w8)) (uf : List w8) :
    List w8 :=
  encode (msgRecs type to frm term logTerm index ents commit snap reject rejectHint ctx vote resps) uf

/-! ## `Message` and its sub-messages: the decoding

Every message is decoded at a recursion depth (`unmarshalPointer`'s `opts.depth`: `proto.Unmarshal`
starts at `DefaultRecursionLimit`, 10000, and each message decrements it, an error below 0): `d`
here is the depth before the decrement, `0` an error; a sub-message is decoded at `d - 1`. Only a
`Message`'s `responses` nest without bound. -/

/-- What a `ConfState`'s getters return. -/
structure CSDec where
  voters : List w64
  learners : List w64
  votersOutgoing : List w64
  learnersNext : List w64
  autoLeave : Bool
  deriving DecidableEq, Repr

/-- What a `SnapshotMetadata`'s getters return (`GetConfState()` of a nil one read as the zero
record). -/
structure MetaDec where
  cs : CSDec
  index : w64
  term : w64
  deriving DecidableEq, Repr

/-- What a `Snapshot`'s getters return (`GetMetadata()` of a nil one read as the zero record). -/
structure SnapDec where
  data : List w8
  md : MetaDec
  deriving DecidableEq, Repr

/-- What a `Message`'s getters return (an entry as `entDecodeRaw`'s tuple, the snapshot `none` if
`nil`), and how many responses it has. -/
structure MsgDec where
  type : w32
  to : w64
  frm : w64
  term : w64
  logTerm : w64
  index : w64
  ents : List (w64 × w64 × w32 × List w8)
  commit : w64
  snap : Option SnapDec
  reject : Bool
  rejectHint : w64
  ctx : List w8
  vote : w64
  nresps : Nat
  deriving DecidableEq, Repr

def csDecZero : CSDec := ⟨[], [], [], [], false⟩

def metaDecZero : MetaDec := ⟨csDecZero, 0, 0⟩

/-- A repeated `uint64`'s values as `w64`s. -/
def repW64 (ks : List (Nat × FVal)) (num : Nat) : Option (List w64) :=
  (repVarint ks num).map (·.map (BitVec.ofNat 64))

/-- **`proto.Unmarshal` of a `ConfState` field's occurrences** at depth `d`: the zero record if
none. -/
def csDecodeD (d : Nat) (parts : List (List w8)) : Option CSDec :=
  if parts = [] then some csDecZero
  else if d = 0 then none
  else
    match decodeMerged csSchema parts with
    | none => none
    | some (ks, _) =>
      match repW64 ks 1, repW64 ks 2, repW64 ks 3, repW64 ks 4 with
      | some v, some l, some vo, some ln => some ⟨v, l, vo, ln, lastBool ks 5⟩
      | _, _, _, _ => none

/-- **`proto.Unmarshal` of a `SnapshotMetadata` field's occurrences** at depth `d`. -/
def metaDecodeD (d : Nat) (parts : List (List w8)) : Option MetaDec :=
  if parts = [] then some metaDecZero
  else if d = 0 then none
  else
    match decodeMerged metaSchema parts with
    | none => none
    | some (ks, _) =>
      (csDecodeD (d - 1) (allLen ks 1)).map fun cs =>
        ⟨cs, BitVec.ofNat 64 ((lastVarint ks 2).getD 0), BitVec.ofNat 64 ((lastVarint ks 3).getD 0)⟩

/-- **`proto.Unmarshal` of a `Snapshot` field's occurrences** at depth `d`: `some none` if none
(`nil`). -/
def snapDecodeD (d : Nat) (parts : List (List w8)) : Option (Option SnapDec) :=
  if parts = [] then some none
  else if d = 0 then none
  else
    match decodeMerged snapSchema parts with
    | none => none
    | some (ks, _) =>
      (metaDecodeD (d - 1) (allLen ks 2)).map fun m => some ⟨(lastLen ks 1).getD [], m⟩

/-- An entry (a repeated field's element: a fresh message each) at depth `d`. -/
def entDecodeD (d : Nat) (bs : List w8) : Option (w64 × w64 × w32 × List w8) :=
  if d = 0 then none else entDecodeRaw bs

/-- **`proto.Unmarshal` of a `Message`** at depth `d` (`none`: an error). -/
def msgDecodeD : Nat → List w8 → Option MsgDec
  | 0, _ => none
  | d + 1, bs =>
    match decode msgSchema bs with
    | none => none
    | some (ks, _) =>
      match (allLen ks 7).mapM (entDecodeD d), snapDecodeD d (allLen ks 9),
          (allLen ks 14).mapM (msgDecodeD d) with
      | some ents, some snap, some rs =>
        some ⟨BitVec.ofNat 32 ((lastVarint ks 1).getD 0), BitVec.ofNat 64 ((lastVarint ks 2).getD 0),
          BitVec.ofNat 64 ((lastVarint ks 3).getD 0), BitVec.ofNat 64 ((lastVarint ks 4).getD 0),
          BitVec.ofNat 64 ((lastVarint ks 5).getD 0), BitVec.ofNat 64 ((lastVarint ks 6).getD 0),
          ents, BitVec.ofNat 64 ((lastVarint ks 8).getD 0), snap, lastBool ks 10,
          BitVec.ofNat 64 ((lastVarint ks 11).getD 0), (lastLen ks 12).getD [],
          BitVec.ofNat 64 ((lastVarint ks 13).getD 0), rs.length⟩
      | _, _, _ => none

/-- **`proto.Unmarshal` into a `Message`**: its getters, or `none` where it returns an error. -/
def msgDecodeRaw (bs : List w8) : Option MsgDec := msgDecodeD 10000 bs


/-! ## The round trip of `Message` and its sub-messages -/

theorem packedVarints_nil (f : Nat) : packedVarints (f + 1) [] = some [] := by
  simp [packedVarints]

/-- The values of a repeated `uint64` written unpacked. -/
theorem mapM_unpacked (xs : List w64) :
    (xs.map fun v => FVal.varint v.toNat).mapM (fun (v : FVal) =>
      match v with
      | .varint n => some [n]
      | .len bs => packedVarints (bs.length + 1) bs
      | _ => some []) = some (xs.map fun v => [v.toNat]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

theorem flatten_singletons (xs : List w64) :
    (xs.map fun v => [v.toNat]).flatten = xs.map (·.toNat) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem map_ofNat_toNat (xs : List w64) : (xs.map (·.toNat)).map (BitVec.ofNat 64) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem boolVarint_ne (b : Bool) : (boolVarint b != 0) = b := by cases b <;> rfl

theorem boolVarint_lt (b : Bool) : boolVarint b < 2 ^ 64 := by cases b <;> decide

theorem csRecs_ok (v l vo ln : List w64) (al : Option Bool) :
    ∀ p ∈ csRecs v l vo ln al, RecOk csSchema p := by
  intro p hp
  simp only [csRecs, optF, List.mem_append, List.mem_map] at hp
  rcases hp with ((((⟨x, -, rfl⟩ | ⟨x, -, rfl⟩) | ⟨x, -, rfl⟩) | ⟨x, -, rfl⟩) | hp)
  · exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases al <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, boolVarint_lt _⟩

/-- A field's values, in input order. -/
def fvals (ks : List (Nat × FVal)) (n : Nat) : List FVal :=
  ks.filterMap fun p => if p.1 = n then some p.2 else none

def FVal.asVarint : FVal → Option Nat
  | .varint n => some n
  | _ => none

def FVal.asLen : FVal → Option (List w8)
  | .len b => some b
  | _ => none

@[simp] theorem fvals_nil (n : Nat) : fvals [] n = [] := rfl

@[simp] theorem fvals_append (a b : List (Nat × FVal)) (n : Nat) :
    fvals (a ++ b) n = fvals a n ++ fvals b n := by
  simp [fvals, List.filterMap_append]

@[simp] theorem fvals_map {α : Type} (xs : List α) (m n : Nat) (f : α → FVal) :
    fvals (xs.map fun x => (m, f x)) n = if m = n then xs.map f else [] := by
  induction xs with
  | nil => simp [fvals]
  | cons x xs ih =>
    simp only [fvals] at ih ⊢
    by_cases h : m = n <;> simp_all

@[simp] theorem fvals_optF {α : Type} (o : Option α) (m n : Nat) (f : α → FVal) :
    fvals (optF m f o) n = if m = n then (o.map f).toList else [] := by
  cases o <;> by_cases h : m = n <;> simp [optF, fvals, h]

theorem lastVarint_fvals (ks : List (Nat × FVal)) (n : Nat) :
    lastVarint ks n = ((fvals ks n).filterMap FVal.asVarint).getLast? := by
  unfold lastVarint fvals
  congr 1
  induction ks with
  | nil => rfl
  | cons p ks ih =>
    rcases p with ⟨m, v⟩
    by_cases h : m = n <;> cases v <;> simp_all [FVal.asVarint, List.filterMap_cons]

theorem lastLen_fvals (ks : List (Nat × FVal)) (n : Nat) :
    lastLen ks n = ((fvals ks n).filterMap FVal.asLen).getLast? := by
  unfold lastLen fvals
  congr 1
  induction ks with
  | nil => rfl
  | cons p ks ih =>
    rcases p with ⟨m, v⟩
    by_cases h : m = n <;> cases v <;> simp_all [FVal.asLen, List.filterMap_cons]

theorem allLen_fvals (ks : List (Nat × FVal)) (n : Nat) :
    allLen ks n = (fvals ks n).filterMap FVal.asLen := by
  unfold allLen fvals
  induction ks with
  | nil => rfl
  | cons p ks ih =>
    rcases p with ⟨m, v⟩
    by_cases h : m = n <;> cases v <;> simp_all [FVal.asLen, List.filterMap_cons]

theorem repVarint_fvals (ks : List (Nat × FVal)) (n : Nat) :
    repVarint ks n = ((fvals ks n).mapM fun (v : FVal) =>
      match v with
      | .varint n => some [n]
      | .len bs => packedVarints (bs.length + 1) bs
      | _ => some []).map List.flatten := rfl

theorem csDecodeD_enc (d : Nat) (hd : d ≠ 0) (v l vo ln : List w64) (al : Option Bool) (uf : List w8)
    (hu : ufWire csSchema uf) :
    csDecodeD d [csEncRaw v l vo ln al uf] = some ⟨v, l, vo, ln, al.getD false⟩ := by
  simp only [csDecodeD, csEncRaw, decodeMerged_single, decode_encode (csRecs_ok v l vo ln al) hu,
    hd, ite_false, List.cons_ne_nil]
  simp only [repW64, repVarint_fvals, lastBool, lastVarint_fvals, csRecs, fvals_append, fvals_map,
    fvals_optF]
  simp only [show (1 : Nat) ≠ 2 by decide, show (1 : Nat) ≠ 3 by decide, show (1 : Nat) ≠ 4 by decide,
    show (2 : Nat) ≠ 1 by decide, show (2 : Nat) ≠ 3 by decide, show (2 : Nat) ≠ 4 by decide,
    show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, show (3 : Nat) ≠ 4 by decide,
    show (4 : Nat) ≠ 1 by decide, show (4 : Nat) ≠ 2 by decide, show (4 : Nat) ≠ 3 by decide,
    show (5 : Nat) ≠ 1 by decide, show (5 : Nat) ≠ 2 by decide, show (5 : Nat) ≠ 3 by decide,
    show (5 : Nat) ≠ 4 by decide, ite_true, ite_false, List.append_nil, List.nil_append,
    mapM_unpacked, Option.map_some, flatten_singletons, map_ofNat_toNat]
  cases al <;> simp [FVal.asVarint, boolVarint_ne]


theorem metaRecs_ok (cs : Option (List w8)) (index term : Option w64)
    (hc : ∀ b, cs = some b → b.length < 2 ^ 64) : ∀ p ∈ metaRecs cs index term, RecOk metaSchema p := by
  intro p hp
  simp only [metaRecs, optF, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · cases h : cs <;> simp [h] at hp; subst hp
    exact ⟨by simp, by simp, rfl, hc _ h⟩
  · cases index <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases term <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩

theorem metaDecodeD_enc (d : Nat) (hd : d ≠ 0) (cs : Option (List w8)) (index term : Option w64)
    (uf : List w8) (hu : ufWire metaSchema uf) (hc : ∀ b, cs = some b → b.length < 2 ^ 64)
    (csd : CSDec) (hcs : csDecodeD (d - 1) cs.toList = some csd) :
    metaDecodeD d [metaEncRaw cs index term uf] =
      some ⟨csd, index.getD 0, term.getD 0⟩ := by
  simp only [metaDecodeD, metaEncRaw, decodeMerged_single, decode_encode (metaRecs_ok cs index term hc) hu,
    hd, ite_false, List.cons_ne_nil]
  have e : allLen (metaRecs cs index term) 1 = cs.toList := by
    rw [allLen_fvals]; cases cs <;> simp [metaRecs, FVal.asLen]
  rw [e, hcs]
  cases index <;> cases term <;> simp [lastVarint_fvals, metaRecs, FVal.asVarint]

theorem snapRecs_ok (data md : Option (List w8)) (hd : ∀ b, data = some b → b.length < 2 ^ 64)
    (hm : ∀ b, md = some b → b.length < 2 ^ 64) : ∀ p ∈ snapRecs data md, RecOk snapSchema p := by
  intro p hp
  simp only [snapRecs, optF, List.mem_append] at hp
  rcases hp with hp | hp
  · cases h : data <;> simp [h] at hp; subst hp
    exact ⟨by simp, by simp, rfl, hd _ h⟩
  · cases h : md <;> simp [h] at hp; subst hp
    exact ⟨by simp, by simp, rfl, hm _ h⟩

theorem snapDecodeD_enc (d : Nat) (hd0 : d ≠ 0) (data md : Option (List w8)) (uf : List w8)
    (hu : ufWire snapSchema uf) (hd : ∀ b, data = some b → b.length < 2 ^ 64)
    (hm : ∀ b, md = some b → b.length < 2 ^ 64)
    (m : MetaDec) (hmd : metaDecodeD (d - 1) md.toList = some m) :
    snapDecodeD d [snapEncRaw data md uf] = some (some ⟨data.getD [], m⟩) := by
  simp only [snapDecodeD, snapEncRaw, decodeMerged_single, decode_encode (snapRecs_ok data md hd hm) hu,
    hd0, ite_false, List.cons_ne_nil]
  have e : allLen (snapRecs data md) 2 = md.toList := by
    rw [allLen_fvals]; cases md <;> cases data <;> simp [snapRecs, FVal.asLen]
  rw [e, hmd]
  cases data <;> simp [lastLen_fvals, snapRecs, FVal.asLen]

theorem msgRecs_ok (type : Option w32) (to frm term logTerm index : Option w64) (ents : List (List w8))
    (commit : Option w64) (snap : Option (List w8)) (reject : Option Bool) (rejectHint : Option w64)
    (ctx : Option (List w8)) (vote : Option w64) (resps : List (List w8))
    (he : ∀ b ∈ ents, b.length < 2 ^ 64) (hs : ∀ b, snap = some b → b.length < 2 ^ 64)
    (hc : ∀ b, ctx = some b → b.length < 2 ^ 64) (hr : ∀ b ∈ resps, b.length < 2 ^ 64) :
    ∀ p ∈ msgRecs type to frm term logTerm index ents commit snap reject rejectHint ctx vote resps,
      RecOk msgSchema p := by
  intro p hp
  simp only [msgRecs, optF, List.mem_append, List.mem_map] at hp
  rcases hp with ((((((((((((hp | hp) | hp) | hp) | hp) | hp) | ⟨e, he', rfl⟩) | hp) | hp) | hp) | hp) | hp) | hp) | ⟨r, hr', rfl⟩
  · cases type <;> simp at hp; subst hp
    exact ⟨by simp, by simp, rfl, enumVarint_lt _⟩
  all_goals first
    | exact ⟨by simp, by simp, rfl, he _ he'⟩
    | exact ⟨by simp, by simp, rfl, hr _ hr'⟩
    | skip
  · cases to <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases frm <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases term <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases logTerm <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases index <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases commit <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases h : snap <;> simp [h] at hp; subst hp; exact ⟨by simp, by simp, rfl, hs _ h⟩
  · cases reject <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, boolVarint_lt _⟩
  · cases rejectHint <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩
  · cases h : ctx <;> simp [h] at hp; subst hp; exact ⟨by simp, by simp, rfl, hc _ h⟩
  · cases vote <;> simp at hp; subst hp; exact ⟨by simp, by simp, rfl, BitVec.isLt _⟩

theorem filterMap_asLen_map (xs : List (List w8)) : (xs.map FVal.len).filterMap FVal.asLen = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [FVal.asLen, ih]

theorem ofNat_lastVarint_opt (o : Option w64) :
    BitVec.ofNat 64 ((((o.map fun v => FVal.varint v.toNat).toList).filterMap FVal.asVarint).getLast?.getD 0) =
      o.getD 0 := by
  cases o <;> simp [FVal.asVarint]

/-- **The message round trip**: `Unmarshal(Marshal(m))` at depth `d + 1` gives the getters of the
fields as set, for entries, a snapshot and responses that decode at depth `d`. -/
theorem msgDecodeD_enc (d : Nat) (type : Option w32) (to frm term logTerm index : Option w64)
    (ents : List (List w8)) (commit : Option w64) (snap : Option (List w8)) (reject : Option Bool)
    (rejectHint : Option w64) (ctx : Option (List w8)) (vote : Option w64) (resps : List (List w8))
    (uf : List w8) (hu : ufWire msgSchema uf)
    (he : ∀ b ∈ ents, b.length < 2 ^ 64) (hs : ∀ b, snap = some b → b.length < 2 ^ 64)
    (hc : ∀ b, ctx = some b → b.length < 2 ^ 64) (hr : ∀ b ∈ resps, b.length < 2 ^ 64)
    (es : List (w64 × w64 × w32 × List w8)) (hes : ents.mapM (entDecodeD d) = some es)
    (sn : Option SnapDec) (hsn : snapDecodeD d snap.toList = some sn)
    (rs : List MsgDec) (hrs : resps.mapM (msgDecodeD d) = some rs) :
    msgDecodeD (d + 1) (msgEncRaw type to frm term logTerm index ents commit snap reject rejectHint ctx
      vote resps uf) =
      some ⟨type.getD 0, to.getD 0, frm.getD 0, term.getD 0, logTerm.getD 0, index.getD 0, es,
        commit.getD 0, sn, reject.getD false, rejectHint.getD 0, ctx.getD [], vote.getD 0, rs.length⟩ := by
  simp only [msgDecodeD, msgEncRaw,
    decode_encode (msgRecs_ok type to frm term logTerm index ents commit snap reject rejectHint ctx vote
      resps he hs hc hr) hu]
  simp only [allLen_fvals, lastVarint_fvals, lastLen_fvals, lastBool, msgRecs, fvals_append, fvals_map,
    fvals_optF]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, List.append_nil, List.nil_append,
    filterMap_asLen_map, ofNat_lastVarint_opt]
  have e9 : (Option.toList (snap.map FVal.len)).filterMap FVal.asLen = snap.toList := by
    cases snap <;> simp [FVal.asLen]
  have e12 : (Option.toList (ctx.map FVal.len)).filterMap FVal.asLen = ctx.toList := by
    cases ctx <;> simp [FVal.asLen]
  rw [e9, e12, hes, hsn, hrs]
  simp only
  congr 1
  cases type <;> cases reject <;> cases ctx <;> simp [FVal.asVarint, ofNat_enumVarint, boolVarint_ne]

end EtcdGrove
end Perennial
