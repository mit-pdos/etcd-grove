import EtcdGrove.Btree.Spec.NewG
import EtcdGrove.Btree.Spec.NewFreeListG
import EtcdGrove.Btree.Spec.NewWithFreeListG

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

theorem NewG.wp_proof
    (wp_NewFreeListG : NewFreeListG.spec (GF := GF) (hG := hG))
    (wp_NewWithFreeListG : NewWithFreeListG.spec (GF := GF) (hG := hG)) :
    NewG.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ K o degree less Hd1 Hd2
  wp_start as #Hless
  wp_auto
  wp_apply (wp_NewFreeListG (V := V) (T := T) (W64 32) (by decide)) as %f #Hf
  wp_apply (wp_NewWithFreeListG (V := V) (T := T) o degree less f Hd1 Hd2) $$ [$Hless $Hf]
    as %t Ht
  wp_end

end proof

end Btree
end EtcdGrove
end Perennial
