/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.needAdminPermission

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.needAdminPermission.wp_proof :
    apply.needAdminPermission.spec (GF := GF) (hG := hG) := by
  intro p rq
  wp_start as #Hr
  iunfold apply.internalRaftRequestIs at Hr
  simp only [apply.presentIs]
  icases Hr with ⟨%Hpn, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%l1, #F1, %H1⟩, ⟨%l2, #F2, %H2⟩, -, -, ⟨%l3, #F3, %H3⟩, ⟨%l4, #F4, %H4⟩, -,
    ⟨%l5, #F5, %H5⟩, ⟨%l6, #F6, %H6⟩, ⟨%l7, #F7, %H7⟩, ⟨%l12, #F12, %H12⟩, ⟨%l13, #F13, %H13⟩,
    ⟨%l8, #F8, %H8⟩, ⟨%l11, #F11, %H11⟩, -, ⟨%l9, #F9, %H9⟩, ⟨%l10, #F10, %H10⟩, -, -, -, -⟩
  wp_auto
  by_cases h1 : l1 = null
  case neg =>
    simp only [h1, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H1.1 h1]
  simp only [h1, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h2 : l2 = null
  case neg =>
    simp only [h2, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H2.1 h2]
  simp only [h2, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h3 : l3 = null
  case neg =>
    simp only [h3, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H3.1 h3]
  simp only [h3, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h4 : l4 = null
  case neg =>
    simp only [h4, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H4.1 h4]
  simp only [h4, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h5 : l5 = null
  case neg =>
    simp only [h5, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H5.1 h5]
  simp only [h5, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h6 : l6 = null
  case neg =>
    simp only [h6, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H6.1 h6]
  simp only [h6, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h7 : l7 = null
  case neg =>
    simp only [h7, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H7.1 h7]
  simp only [h7, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h8 : l8 = null
  case neg =>
    simp only [h8, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H8.1 h8]
  simp only [h8, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h9 : l9 = null
  case neg =>
    simp only [h9, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H9.1 h9]
  simp only [h9, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h10 : l10 = null
  case neg =>
    simp only [h10, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H10.1 h10]
  simp only [h10, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h11 : l11 = null
  case neg =>
    simp only [h11, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H11.1 h11]
  simp only [h11, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h12 : l12 = null
  case neg =>
    simp only [h12, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H12.1 h12]
  simp only [h12, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  by_cases h13 : l13 = null
  case neg =>
    simp only [h13, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ; ipureintro; simp [apply.needAdminPermission, H13.1 h13]
  simp only [h13, decide_true, Bool.not_true, Bool.true_eq_false, decide_false]
  wp_auto
  iapply HΦ; ipureintro
  simp_all [apply.needAdminPermission]

end proof

end EtcdGrove
end Perennial
