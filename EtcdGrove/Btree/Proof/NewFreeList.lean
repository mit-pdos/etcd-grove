import EtcdGrove.Btree.Spec.NewFreeList
import EtcdGrove.Btree.Spec.NewFreeListG

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

theorem NewFreeList.wp_proof (wp_NewFreeListG : NewFreeListG.spec (GF := GF) (hG := hG)) :
    NewFreeList.spec (GF := GF) (hG := hG) := by
  intro size Hsize
  wp_start
  wp_auto
  wp_apply (wp_NewFreeListG (V := GoInterface) (T := Item.ty) size Hsize) as %f #Hf
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
