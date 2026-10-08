import EtcdGrove.Btree.Spec.NewOrderedG
import EtcdGrove.Btree.Spec.Less
import EtcdGrove.Btree.Spec.NewG

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

theorem NewOrderedG.wp_proof
    (wp_Less : Less.spec (GF := GF) (hG := hG))
    (wp_NewG : NewG.spec (GF := GF) (hG := hG)) :
    NewOrderedG.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ ltb hord hlt degree Hd1 Hd2
  wp_start
  wp_auto
  wp_apply (wp_Less (V := V) (T := T) ltb hord hlt) as %less #Hless
  wp_apply (wp_NewG (V := V) (T := T) (orderedOrder _ hord) degree less Hd1 Hd2) $$ [$Hless]
    as %t Ht
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
