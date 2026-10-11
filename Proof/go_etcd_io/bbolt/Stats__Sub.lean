module
public import Spec.go_etcd_io.bbolt.Stats__Sub
public import Spec.go_etcd_io.bbolt.TxStats__Sub

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
theorem Stats.Sub.wp_proof (hSub : TxStats.Sub.spec (GF := GF) (hG := hG)) :
    Stats.Sub.spec (GF := GF) (hG := hG) := by
  intro l o v w dq1 dq2
  wp_start as ⟨Hl, Ho⟩
  by_cases ho : o = null
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ho)]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ho)]
    subst ho
    wp_auto
    iapply HΦ; iframe
    ipureintro; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ho)]
    rw [ite_eq_right_of_eq_false _ _ (eq_false ho)]
    ihave %Hnl := typedPointsto_not_null _ _ _ $$ Hl
    ihave %Hno := typedPointsto_not_null _ _ _ $$ Ho
    iStructNamedSuffix Hl "_s"
    iStructNamedSuffix Ho "_o"
    wp_auto
    rw [decide_eq_false ho]
    try wp_auto
    wp_apply hSub $$ [$TxStats_s $TxStats_o] as %dts ⟨%Hdts, TxStats_s, TxStats_o⟩
    try wp_auto
    iapply HΦ
    rw [typedPointsto_unseal_eq l, typedPointsto_unseal_eq o]
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    ipureintro
    refine ⟨?_, Hnl, Hno⟩
    subst Hdts; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
