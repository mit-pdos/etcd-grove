import EtcdGrove.Btree.Spec.BTreeG__Has
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

theorem BTreeG.Has.wp_proof (wp_Get : BTreeG.Get.spec (GF := GF) (hG := hG)) :
    BTreeG.Has.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t dq s key k
  wp_start as ⟨Ht, #Hk⟩
  wp_auto
  wp_apply wp_Get o t dq s key k $$ [Ht] as Ht
  · iframe # ∗
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
