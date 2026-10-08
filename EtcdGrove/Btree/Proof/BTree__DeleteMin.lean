import EtcdGrove.Btree.Spec.BTree__DeleteMin
import EtcdGrove.Btree.Spec.BTreeG__DeleteMin

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

theorem BTree.DeleteMin.wp_proof (wp_BTreeG_DeleteMin : BTreeG.DeleteMin.spec (GF := GF) (hG := hG)) :
    BTree.DeleteMin.spec (GF := GF) (hG := hG) := by
  intro K o t s
  wp_start as H0
  wp_auto
  wp_apply (wp_BTreeG_DeleteMin (V := GoInterface) (T := Item.ty) o t s) $$ [$H0] as Hp0
  simp only [removeOp]
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
