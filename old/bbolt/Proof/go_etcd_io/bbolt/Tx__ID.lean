module
public import Spec.go_etcd_io.bbolt.Tx__ID
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid

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

theorem Tx.ID.wp_proof (hTxid : _root_.Perennial.EtcdGrove.bbolt.Meta.Txid.spec (GF := GF) (hG := hG)) :
    Tx.ID.spec (GF := GF) (hG := hG) := by
  intro tl t dq m dq2
  wp_start as H
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  by_cases htl : tl = null
  · rw [ite_eq_left_of_eq_true _ _ (eq_true htl)] at *
    rw [ite_eq_left_of_eq_true _ _ (eq_true htl)]
    subst htl
    wp_auto
    iapply HΦ; itrivial
  · rw [ite_eq_right_of_eq_false _ _ (eq_false htl)]
    rw [ite_eq_right_of_eq_false _ _ (eq_false htl)]
    icases H with ⟨Ht, Hm⟩
    wp_auto
    rw [decide_eq_false htl]
    try wp_auto
    by_cases hm : t.meta' = null
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
      rw [decide_eq_true hm]
      try wp_auto
      iapply HΦ; iframe
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
      rw [decide_eq_false hm]
      try wp_auto
      wp_apply hTxid $$ [$Hm] as Hm
      try wp_auto
      iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
