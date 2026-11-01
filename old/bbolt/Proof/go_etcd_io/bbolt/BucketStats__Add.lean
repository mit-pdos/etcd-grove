module
public import Spec.go_etcd_io.bbolt.BucketStats__Add

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxHeartbeats 400000 in
theorem BucketStats.Add.wp_proof : BucketStats.Add.spec (GF := GF) (hG := hG) := by
  intro l v o
  wp_start as Hl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  wp_auto
  wp_if_destruct
  all_goals
    try wp_auto
    iapply HΦ
    first
      | rw [ite_eq_left_of_eq_true _ _ (eq_true (by assumption))]
      | rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
    rw [typedPointsto_unseal_eq l]
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    ipureintro; exact Hnn

end proof

end bbolt
end EtcdGrove
end Perennial
