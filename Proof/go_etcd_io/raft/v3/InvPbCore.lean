/-
The declarations `pbN`, `pbMsg`, `pbMsg_persistent`, `pbMsg_ufWire`, `pbMsg_alloc` of
`Proof/go_etcd_io/raft/v3/InvPb.lean`, split from it so that the WAL
(`Proof/go_etcd_io/etcd/server/v3/storage/wal/`) imports them without the rest (until 2026-11-15 an
extract of `etc/gen-part-copies.py` for the part `LinuxFs/`; notes/wal-lean-integration.md). The
source imports this module.
-/
module

public import Proof.go_etcd_io.raft.v3.PbModel
public import Proof.google_golang_org.protobuf.proto.PbSchema
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import GeneratedProof.go_etcd_io.raft.v3.raftpb

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
generated message), its unknown fields' bytes `uf`: an invariant only the `proto.*` axioms take
(see the file header), and `uf` as protobuf-go's decoder leaves it at the type's schema
(`ufWire (pbSchemaOf (PbGoType.goTy T)) uf`, `PbSchema.lean`; `[v6a]` 3): what a frozen message's
wire content reads its unknown fields' validity from. -/
def pbMsg (T : Type) [PbGoType T] (l : Loc) (uf : List w8) : IProp GF :=
  iprop(inv pbN iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32)
      (us : GoSlice),
    l.[T, go!"state"] ↦ st ∗ l.[T, go!"sizeCache"] ↦ sc ∗ l.[T, go!"unknownFields"] ↦ us ∗
      us ↦* uf) ∗ ⌜ufWire (pbSchemaOf (PbGoType.goTy T)) uf⌝)

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

/-- The hidden fields of a protobuf object made into its invariant (once, at allocation). -/
theorem pbMsg_alloc (T : Type) [PbGoType T] (l : Loc)
    (st : google_golang_org.protobuf.internal.impl.MessageState)
    (sc : w32) (us : GoSlice) (uf : List w8) (E : CoPset)
    (huf : ufWire (pbSchemaOf (PbGoType.goTy T)) uf) :
    (l.[T, go!"state"] ↦ st ∗ l.[T, go!"sizeCache"] ↦ sc ∗ l.[T, go!"unknownFields"] ↦ us ∗
      us ↦* uf : IProp GF) ⊢ |={E}=> pbMsg T l uf := by
  iintro ⟨H1, H2, H3, H4⟩
  unfold pbMsg
  ihave Hi : |={E}=> inv pbN iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    l.[T, go!"state"] ↦ st ∗ l.[T, go!"sizeCache"] ↦ sc ∗ l.[T, go!"unknownFields"] ↦ us ∗
      us ↦* uf) $$ [H1 H2 H3 H4]
  · iapply inv_alloc
    inext
    iexists st, sc, us
    iframe
  imod Hi with #Hi
  imodintro
  iframe Hi
  ipureintro; exact huf

end extract

end EtcdGrove
end Perennial
