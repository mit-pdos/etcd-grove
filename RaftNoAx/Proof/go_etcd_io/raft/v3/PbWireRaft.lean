-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/PbWireRaft.lean` (etc/copy-part.py; rerun it, do not edit).
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
public import RaftNoAx.Proof.google_golang_org.protobuf.proto.PbSchema

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

end EtcdGrove
end Perennial
