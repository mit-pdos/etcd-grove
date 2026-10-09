module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.New
public import Spec.k8s_io.utils.third_party.forked.golang.btree.NewFreeList
public import Spec.k8s_io.utils.third_party.forked.golang.btree.NewWithFreeList

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

theorem New.wp_proof
    (wp_NewFreeListG : NewFreeList.spec (GF := GF) (hG := hG))
    (wp_NewWithFreeListG : NewWithFreeList.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o degree less Hd1 Hd2
  wp_start as #Hless
  wp_auto
  wp_apply (wp_NewFreeListG (V := V) (T := T) (W64 32) (by decide)) as %f #Hf
  wp_apply (wp_NewWithFreeListG (V := V) (T := T) o degree less f Hd1 Hd2) $$ [$Hless $Hf]
    as %t Ht
  wp_end

end proof

end btree
end EtcdGrove
end Perennial
