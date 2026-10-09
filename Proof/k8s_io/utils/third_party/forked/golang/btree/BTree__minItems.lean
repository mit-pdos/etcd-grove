module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__minItems

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

theorem BTree.minItems.wp_proof : BTree.minItems.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ t dq tv
  wp_start as Ht
  icases (Access.access (A := t.[BTree V, go!"degree"] ↦{dq} tv.degree')
      (A' := t.[BTree V, go!"degree"] ↦{dq} tv.degree') (P := t ↦{dq} tv)) $$ Ht
    with ⟨Hd, Hback⟩
  wp_auto
  ihave Ht := Hback $$ Hd
  wp_end

end proof

end btree
end EtcdGrove
end Perennial
