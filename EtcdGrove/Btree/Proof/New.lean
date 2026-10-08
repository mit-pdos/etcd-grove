import EtcdGrove.Btree.Spec.New
import EtcdGrove.Btree.Spec.NewG
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

theorem New.wp_proof (wp_NewG : NewG.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro K o degree H1 H2
  wp_start as #Ho
  ihave #Hinit := isInit_access $$ Hpkg
  unfold isInit
  icases Hinit with ⟨%f, #Hf, #Hless⟩
  wp_auto
  ihave #Hl := isLess_itemLess o f $$ [Hless Ho]
  · isplit <;> iassumption
  wp_apply (wp_NewG (V := GoInterface) (T := Item.ty) o degree f H1 H2) $$ [] as %t Ht
  · iexact Hl
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
