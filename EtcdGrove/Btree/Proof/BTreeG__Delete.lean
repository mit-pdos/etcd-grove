import EtcdGrove.Btree.Spec.BTreeG__Delete
import EtcdGrove.Btree.Spec.BTreeG__deleteItem

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

theorem BTreeG.Delete.wp_proof (wp_deleteItem : BTreeG.deleteItem.spec (GF := GF) (hG := hG)) :
    BTreeG.Delete.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t s item k
  wp_start as ⟨Ht, #Hk⟩
  wp_auto
  wp_apply wp_deleteItem o t s item (.key k) (W64 0) rfl $$ [$Ht] as Ht
  · simp only [targetItem]; iexact Hk
  simp only [removeOp]
  iapply HΦ $$ Ht

end proof

end Btree
end EtcdGrove
end Perennial
