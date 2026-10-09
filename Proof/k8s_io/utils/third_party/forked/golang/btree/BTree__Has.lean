module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Has
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Get

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem BTree.Has.wp_proof (wp_Get : BTree.Get.spec (GF := GF) (hG := hG)) :
    BTree.Has.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t dq s key k
  wp_start as ⟨Ht, #Hk⟩
  wp_auto
  wp_apply wp_Get o t dq s key k $$ [Ht] as Ht
  · iframe # ∗
  wp_end

end proof

end btree
end EtcdGrove
end Perennial
