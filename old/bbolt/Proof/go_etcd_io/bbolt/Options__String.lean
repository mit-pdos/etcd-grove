module
public import Spec.go_etcd_io.bbolt.Options__String
public import Perennial.Proof.fmt

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
theorem Options.String.wp_proof : Options.String.spec (GF := GF) (hG := hG) := by
  intro ol v dq
  wp_start as Ho
  by_cases ho : ol = null
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ho)]
    subst ho
    wp_auto
    iapply HΦ; iframe
    ipureintro; intro _; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ho)]
    wp_auto
    rw [decide_eq_false ho]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply fmt.wp_Sprintf as %s _
    iapply HΦ; iframe
    ipureintro; intro h; exact absurd h ho

end proof

end bbolt
end EtcdGrove
end Perennial
