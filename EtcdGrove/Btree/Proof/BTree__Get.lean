import EtcdGrove.Btree.Spec.BTree__Get
import EtcdGrove.Btree.Spec.BTreeG__Get

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

theorem BTree.Get.wp_proof (wp_BTreeG_Get : BTreeG.Get.spec (GF := GF) (hG := hG)) :
    BTree.Get.spec (GF := GF) (hG := hG) := by
  intro K o t dq s key k
  wp_start as ⟨H0, H1⟩
  wp_auto
  wp_apply (wp_BTreeG_Get (V := GoInterface) (T := Item.ty) o t dq s key k) $$ [$H0 $H1] as Hp0
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
