module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.NewOrdered
public import Spec.k8s_io.utils.third_party.forked.golang.btree.Less
public import Spec.k8s_io.utils.third_party.forked.golang.btree.New

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

theorem NewOrdered.wp_proof
    (wp_Less : Less.spec (GF := GF) (hG := hG))
    (wp_NewG : New.spec (GF := GF) (hG := hG)) :
    NewOrdered.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ ltb hord hlt degree Hd1 Hd2
  wp_start
  wp_auto
  wp_apply (wp_Less (V := V) (T := T) ltb hord hlt) as %less #Hless
  wp_apply (wp_NewG (V := V) (T := T) (orderedOrder _ hord) degree less Hd1 Hd2) $$ [$Hless]
    as %t Ht
  wp_end

end proof

end btree
end EtcdGrove
end Perennial
