module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__DeleteMin
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__deleteItem

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

theorem BTree.DeleteMin.wp_proof (wp_deleteItem : BTree.deleteItem.spec (GF := GF) (hG := hG)) :
    BTree.DeleteMin.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o t s
  wp_start as Ht
  wp_auto
  wp_apply wp_deleteItem o t s _ .min (W64 1) rfl $$ [$Ht] as Ht
  · simp only [targetItem]; itrivial
  simp only [removeOp]
  iapply HΦ $$ Ht

end proof

end btree
end EtcdGrove
end Perennial
