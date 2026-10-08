import EtcdGrove.Btree.Spec.NewWithFreeList
import EtcdGrove.Btree.Spec.NewWithFreeListG
import EtcdGrove.Btree.Lemmas.Item

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

theorem NewWithFreeList.wp_proof
    (wp_NewWithFreeListG : NewWithFreeListG.spec (GF := GF) (hG := hG)) :
    NewWithFreeList.spec (GF := GF) (hG := hG) := by
  intro K o degree f H1 H2
  wp_start as ⟨#Ho, #Hfl⟩
  ihave #Hinit := isInit_access $$ Hpkg
  unfold isInit
  icases Hinit with ⟨%less, #Hlv, #Hless⟩
  wp_auto
  ihave #Hl := isLess_itemLess o less $$ [Hless Ho]
  · isplit <;> iassumption
  wp_apply (wp_NewWithFreeListG (V := GoInterface) (T := Item.ty) o degree less f H1 H2) $$ []
    as %t Ht
  · isplit <;> iassumption
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
