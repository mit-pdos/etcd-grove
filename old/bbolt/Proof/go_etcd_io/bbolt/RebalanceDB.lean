/-
The writer's view, from the database (`dbWR`): its pages' slots are disjoint and page 0 is
not one of them (a meta page: no view covers slots 0 and 1), what `node.free` and the
rebalance of a bucket need.
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceFree
public import Proof.go_etcd_io.bbolt.WriteAlloc
public import Proof.go_etcd_io.bbolt.DBRemap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The writer's view's facts, out of the database. -/
theorem dbWR_view (I : FLImpl (GF := GF)) (γd : DBNames) (W : WView) (txl : Loc) (txid : w64)
    (ρ : DBState) :
    dbWR I γd W txl txid ρ ⊢ ⌜pagesDisjoint W.pages ∧ W.pages !! 0 = none⌝ := by
  unfold dbWR
  iintro ⟨Hdb, %Hd⟩
  obtain ⟨-, -, -, -, -, w, hw, hwp, -, -, -, -⟩ := Hd
  isimp only [ownDB] at Hdb
  iNamed Hdb
  ipureintro
  have hr := writer_readerOK ρ v0 v1 Hok w hw
  have hm := (Hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 w hw).2
  rw [← hwp]
  refine ⟨hr.2.1, ?_⟩
  cases h0 : w.pages !! 0 with
  | none => rfl
  | some pg =>
    have := (hm.2 0 ⟨0, pg, h0, Nat.le_refl _, by omega⟩).1
    omega

theorem dbWR_view_keep (I : FLImpl (GF := GF)) (γd : DBNames) (W : WView) (txl : Loc) (txid : w64)
    (ρ : DBState) :
    dbWR I γd W txl txid ρ ⊢ dbWR I γd W txl txid ρ ∗ ⌜pagesDisjoint W.pages ∧ W.pages !! 0 = none⌝ := by
  have : Persistent (iprop(⌜pagesDisjoint W.pages ∧ W.pages !! 0 = none⌝) : IProp GF) := inferInstance
  exact persistent_entails_left (dbWR_view I γd W txl txid ρ)

end own

end bbolt
end EtcdGrove
end Perennial
