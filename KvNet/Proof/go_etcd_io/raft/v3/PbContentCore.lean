-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/PbContentCore.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The declarations `EntryC`, `EntryC.model`, `optVarintSize`, `entrySize`, `optCell`, `bytesC`,
`optCell_persistent`, `bytesC_persistent`, `pbMsg_uf_entry`, `entRoC`, `entRoC_persistent` of
`Proof/go_etcd_io/raft/v3/PbContent.lean`, split from it so that the WAL
(`Proof/go_etcd_io/etcd/server/v3/storage/wal/`) imports them without the rest (until 2026-11-15 an
extract of `etc/gen-part-copies.py` for the part `LinuxFs/`; notes/wal-lean-integration.md). The
source imports this module.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.PbModel
public import Proof.google_golang_org.protobuf.proto.UfWire
public import KvNet.Proof.go_etcd_io.raft.v3.InvPbCore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- **An `Entry`'s wire content** (see the file header). -/
structure EntryC [GooseExts] where
  term : Option w64
  index : Option w64
  type : Option raftpb.EntryType
  data : Option (List w8)
  uf : List w8

/-- What the getters read of a wire content. -/
def EntryC.model [GooseExts] (c : EntryC) : EntryM :=
  ⟨c.term.getD (zero_val w64), c.index.getD (zero_val w64), c.type.getD (zero_val raftpb.EntryType),
    c.data.getD []⟩

/-- An optional varint field's size: its tag and its value. -/
def optVarintSize (o : Option Nat) : Nat := match o with | none => 0 | some n => 1 + varintSize n

/-- **protobuf's size of an `Entry`** (an enum is an `int32`, sign-extended to 64 bits). -/
def entrySize [GooseExts] (c : EntryC) : Nat :=
  optVarintSize (c.type.map fun t => (uint.Z (W64 (sint.Z t))).toNat) +
  optVarintSize (c.term.map fun v => (uint.Z v).toNat) +
  optVarintSize (c.index.map fun v => (uint.Z v).toNat) +
  (match c.data with | none => 0 | some bs => 1 + varintSize bs.length + bs.length) +
  c.uf.length

section extract
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A proto2 optional scalar's cell, frozen: `nil`, or set (possibly to zero). -/
def optCell {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) : Option V → IProp GF
  | none => iprop(⌜p = null⌝)
  | some v => iprop(p ↦□ v)

/-- A `bytes` field, frozen: `nil`, or a non-nil slice holding the bytes. -/
def bytesC (ds : GoSlice) : Option (List w8) → IProp GF
  | none => iprop(⌜ds = slice.nil⌝)
  | some bs => iprop(⌜ds ≠ slice.nil⌝ ∗ ds ↦*□ bs)

instance optCell_persistent {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (o : Option V) : Persistent (optCell (GF := GF) p o) := by
  cases o <;> unfold optCell <;> infer_instance

instance bytesC_persistent (ds : GoSlice) (o : Option (List w8)) :
    Persistent (bytesC (GF := GF) ds o) := by
  cases o <;> unfold bytesC <;> infer_instance

/-- An entry's unknown fields are valid at `Entry`'s schema (`pbMsg`'s, `[v6a]` 3). -/
theorem pbMsg_uf_entry (l : Loc) (uf : List w8) :
    pbMsg (GF := GF) raftpb.Entry l uf ⊢ ⌜ufWire entrySchema uf⌝ := by
  have h := pbMsg_ufWire (GF := GF) raftpb.Entry l uf
  rwa [show PbGoType.goTy raftpb.Entry = raftpb.Entry.ty from rfl, pbSchemaOf_entry] at h

/-- **A frozen `*Entry` holding exactly `c`** (see the file header). -/
def entRoC (l : Loc) (c : EntryC) : IProp GF :=
  iprop(∃ (pt pi pty : Loc) (ds : GoSlice),
    ⌜l ≠ null⌝ ∗
    l.[raftpb.Entry, go!"Term"] ↦□ pt ∗ optCell pt c.term ∗
    l.[raftpb.Entry, go!"Index"] ↦□ pi ∗ optCell pi c.index ∗
    l.[raftpb.Entry, go!"Type"] ↦□ pty ∗ optCell pty c.type ∗
    l.[raftpb.Entry, go!"Data"] ↦□ ds ∗ bytesC ds c.data ∗
    pbMsg raftpb.Entry l c.uf)

set_option synthInstance.maxSize 512 in
set_option synthInstance.maxHeartbeats 200000 in
instance entRoC_persistent (l : Loc) (c : EntryC) : Persistent (entRoC (GF := GF) l c) := by
  unfold entRoC; infer_instance

end extract

end EtcdGrove
end Perennial
