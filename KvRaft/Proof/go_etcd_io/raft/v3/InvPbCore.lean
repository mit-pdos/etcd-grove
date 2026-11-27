-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/InvPbCore.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The declarations `pbN`, `pbMsg`, `pbMsg_persistent`, `pbMsg_ufWire`, `pbMsg_alloc` of
`Proof/go_etcd_io/raft/v3/InvPb.lean`, split from it (as in the main tree).

The part's own (raft without hand-written axioms, `notes/raft-noax-part.md`, "Stage 3a"): in the
main tree `pbMsg` is an invariant owning the hidden fields, which only the `proto.*` axioms took
(protobuf's runtime writes `sizeCache`). In the part no code writes a message's hidden fields once
it is allocated (the hand-written `raftpb` clones and `EntrySize` replace `proto.Clone`/`proto.Size`
and only read `unknownFields`), and the clones read the unknown fields' bytes over several steps
(`append(nil, u...)`), which an invariant holding them cannot allow. So `pbMsg` is the hidden fields
frozen: persistent points-tos, the bytes `us ↦*□ uf`. `pbN` stays (unused) so that the copies naming
it still build.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.PbModel
public import KvRaft.Proof.google_golang_org.protobuf.proto.PbSchema
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import KvRaft.GeneratedProof.go_etcd_io.raft.v3.raftpb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section extract
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The namespace of the hidden-field invariants. -/
def pbN : Namespace := nroot.@"protobuf"

/-- **The hidden fields** of the protobuf object at `l` of Go type `T` (the Lean struct of a
generated message), its unknown fields' bytes `uf`: frozen (see the file header), and `uf` as
protobuf-go's decoder leaves it at the type's schema (`ufWire (pbSchemaOf (PbGoType.goTy T)) uf`,
`PbSchema.lean`; `[v6a]` 3): what a frozen message's wire content reads its unknown fields' validity
from. -/
def pbMsg (T : Type) [PbGoType T] (l : Loc) (uf : List w8) : IProp GF :=
  iprop((∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32) (us : GoSlice),
    l.[T, go!"state"] ↦□ st ∗ l.[T, go!"sizeCache"] ↦□ sc ∗ l.[T, go!"unknownFields"] ↦□ us ∗
      us ↦*□ uf) ∗ ⌜ufWire (pbSchemaOf (PbGoType.goTy T)) uf⌝)

instance pbMsg_persistent (T : Type) [PbGoType T] (l : Loc) (uf : List w8) :
    Persistent (pbMsg (GF := GF) T l uf) := by
  unfold pbMsg; infer_instance

omit package_sem in
/-- A message's unknown fields are as the decoder leaves them, at its type's schema. -/
theorem pbMsg_ufWire (T : Type) [PbGoType T] (l : Loc) (uf : List w8) :
    pbMsg (GF := GF) T l uf ⊢ ⌜ufWire (pbSchemaOf (PbGoType.goTy T)) uf⌝ := by
  unfold pbMsg
  iintro ⟨-, %H⟩
  ipureintro; exact H

omit package_sem in
/-- A message's unknown fields, read: the field (frozen) and its bytes (read-only). -/
theorem pbMsg_uf (T : Type) [PbGoType T] (l : Loc) (uf : List w8) :
    pbMsg (GF := GF) T l uf ⊢
      ∃ us : GoSlice, l.[T, go!"unknownFields"] ↦□ us ∗ us ↦*□ uf := by
  unfold pbMsg
  iintro ⟨⟨%st, %sc, %us, -, -, #Hu, #Hb⟩, -⟩
  iexists us
  iframe Hu Hb

/-- The hidden fields of a protobuf object frozen into `pbMsg` (once, at allocation). -/
theorem pbMsg_alloc (T : Type) [PbGoType T] (l : Loc)
    (st : google_golang_org.protobuf.internal.impl.MessageState)
    (sc : w32) (us : GoSlice) (uf : List w8) (E : CoPset)
    (huf : ufWire (pbSchemaOf (PbGoType.goTy T)) uf) :
    (l.[T, go!"state"] ↦ st ∗ l.[T, go!"sizeCache"] ↦ sc ∗ l.[T, go!"unknownFields"] ↦ us ∗
      us ↦* uf : IProp GF) ⊢ |={E}=> pbMsg T l uf := by
  iintro ⟨H1, H2, H3, H4⟩
  ipersist H1
  ipersist H2
  ipersist H3
  ipersist H4
  imodintro
  unfold pbMsg
  isplitl
  · iexists st, sc, us
    iframe H1 H2 H3 H4
  · ipureintro; exact huf

end extract

end EtcdGrove
end Perennial
