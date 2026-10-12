/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/getRequestType.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.getRequestType
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 4000000 in
theorem getRequestType.wp_proof : getRequestType.spec (GF := GF) (hG := hG) := by
  intro p rq
  generalize hn : reqTypeName rq = n
  wp_start as #Hirr
  ihave #Hirr' := Hirr
  iunfold irrNoHdrIs at Hirr'
  icases Hirr' with ⟨%Hpn, -, ⟨%l0, #Hf0, H0⟩, ⟨%l1, #Hf1, H1⟩, ⟨%l2, #Hf2, H2⟩, ⟨%l3, #Hf3, H3⟩, ⟨%l4, #Hf4, H4⟩, ⟨%l5, #Hf5, H5⟩, ⟨%l6, #Hf6, H6⟩, ⟨%l7, #Hf7, H7⟩, ⟨%l8, #Hf8, H8⟩, ⟨%l9, #Hf9, H9⟩, ⟨%l10, #Hf10, H10⟩, ⟨%l11, #Hf11, H11⟩, ⟨%l12, #Hf12, H12⟩, ⟨%l13, #Hf13, H13⟩, ⟨%l14, #Hf14, H14⟩, ⟨%l15, #Hf15, H15⟩, ⟨%l16, #Hf16, H16⟩, ⟨%l17, #Hf17, H17⟩, ⟨%l18, #Hf18, H18⟩, ⟨%l19, #Hf19, H19⟩, ⟨%l20, #Hf20, H20⟩, ⟨%l21, #Hf21, H21⟩, ⟨%l22, #Hf22, H22⟩, ⟨%l23, #Hf23, H23⟩, ⟨%l24, #Hf24, H24⟩, ⟨%l25, #Hf25, H25⟩, ⟨%l26, #Hf26, H26⟩, ⟨%l27, #Hf27, H27⟩, ⟨%l28, #Hf28, H28⟩, ⟨%l29, #Hf29, H29⟩⟩
  ihave %h0 := apply.optReqIs_nil l0 rq.range _ apply.rangeIs_nn $$ H0
  have e0 : rq.range.isSome = !decide (l0 = null) := by
    cases hc : rq.range <;> simp_all
  ihave %h1 := apply.optReqIs_nil l1 rq.put _ apply.putIs_nn $$ H1
  have e1 : rq.put.isSome = !decide (l1 = null) := by
    cases hc : rq.put <;> simp_all
  ihave %h2 := apply.optReqIs_nil l2 rq.deleteRange _ apply.deleteIs_nn $$ H2
  have e2 : rq.deleteRange.isSome = !decide (l2 = null) := by
    cases hc : rq.deleteRange <;> simp_all
  ihave %h3 := apply.optReqIs_nil l3 rq.txn _ apply.txnIs_nn $$ H3
  have e3 : rq.txn.isSome = !decide (l3 = null) := by
    cases hc : rq.txn <;> simp_all
  ihave %h4 := apply.optReqIs_nil l4 rq.compaction _ apply.compactionIs_nn $$ H4
  have e4 : rq.compaction.isSome = !decide (l4 = null) := by
    cases hc : rq.compaction <;> simp_all
  ihave %h5 := apply.optReqIs_nil l5 rq.leaseGrant _ apply.leaseGrantIs_nn $$ H5
  have e5 : rq.leaseGrant.isSome = !decide (l5 = null) := by
    cases hc : rq.leaseGrant <;> simp_all
  ihave %h6 := apply.optReqIs_nil l6 rq.leaseRevoke _ apply.leaseRevokeIs_nn $$ H6
  have e6 : rq.leaseRevoke.isSome = !decide (l6 = null) := by
    cases hc : rq.leaseRevoke <;> simp_all
  ihave %h7 := apply.optReqIs_nil l7 rq.alarm _ apply.alarmRequestIs_nn $$ H7
  have e7 : rq.alarm.isSome = !decide (l7 = null) := by
    cases hc : rq.alarm <;> simp_all
  ihave %h8 := apply.optReqIs_nil l8 rq.leaseCheckpoint _ apply.leaseCheckpointIs_nn $$ H8
  have e8 : rq.leaseCheckpoint.isSome = !decide (l8 = null) := by
    cases hc : rq.leaseCheckpoint <;> simp_all
  iunfold apply.presentIs at H9
  icases H9 with %h9
  have e9 : rq.authEnable = !decide (l9 = null) := by
    cases hc : rq.authEnable <;> simp_all
  iunfold apply.presentIs at H10
  icases H10 with %h10
  have e10 : rq.authDisable = !decide (l10 = null) := by
    cases hc : rq.authDisable <;> simp_all
  iunfold apply.presentIs at H11
  icases H11 with %h11
  have e11 : rq.authStatus = !decide (l11 = null) := by
    cases hc : rq.authStatus <;> simp_all
  ihave %h12 := apply.optReqIs_nil l12 rq.authenticate _ apply.authenticateIs_nn $$ H12
  have e12 : rq.authenticate.isSome = !decide (l12 = null) := by
    cases hc : rq.authenticate <;> simp_all
  iunfold apply.presentIs at H13
  icases H13 with %h13
  have e13 : rq.authUserAdd = !decide (l13 = null) := by
    cases hc : rq.authUserAdd <;> simp_all
  iunfold apply.presentIs at H14
  icases H14 with %h14
  have e14 : rq.authUserDelete = !decide (l14 = null) := by
    cases hc : rq.authUserDelete <;> simp_all
  ihave %h15 := apply.optReqIs_nil l15 rq.authUserGet _ apply.authUserGetIs_nn $$ H15
  have e15 : rq.authUserGet.isSome = !decide (l15 = null) := by
    cases hc : rq.authUserGet <;> simp_all
  iunfold apply.presentIs at H16
  icases H16 with %h16
  have e16 : rq.authUserChangePassword = !decide (l16 = null) := by
    cases hc : rq.authUserChangePassword <;> simp_all
  iunfold apply.presentIs at H17
  icases H17 with %h17
  have e17 : rq.authUserGrantRole = !decide (l17 = null) := by
    cases hc : rq.authUserGrantRole <;> simp_all
  iunfold apply.presentIs at H18
  icases H18 with %h18
  have e18 : rq.authUserRevokeRole = !decide (l18 = null) := by
    cases hc : rq.authUserRevokeRole <;> simp_all
  iunfold apply.presentIs at H19
  icases H19 with %h19
  have e19 : rq.authUserList = !decide (l19 = null) := by
    cases hc : rq.authUserList <;> simp_all
  iunfold apply.presentIs at H20
  icases H20 with %h20
  have e20 : rq.authRoleList = !decide (l20 = null) := by
    cases hc : rq.authRoleList <;> simp_all
  iunfold apply.presentIs at H21
  icases H21 with %h21
  have e21 : rq.authRoleAdd = !decide (l21 = null) := by
    cases hc : rq.authRoleAdd <;> simp_all
  iunfold apply.presentIs at H22
  icases H22 with %h22
  have e22 : rq.authRoleDelete = !decide (l22 = null) := by
    cases hc : rq.authRoleDelete <;> simp_all
  ihave %h23 := apply.optReqIs_nil l23 rq.authRoleGet _ apply.authRoleGetIs_nn $$ H23
  have e23 : rq.authRoleGet.isSome = !decide (l23 = null) := by
    cases hc : rq.authRoleGet <;> simp_all
  iunfold apply.presentIs at H24
  icases H24 with %h24
  have e24 : rq.authRoleGrantPermission = !decide (l24 = null) := by
    cases hc : rq.authRoleGrantPermission <;> simp_all
  iunfold apply.presentIs at H25
  icases H25 with %h25
  have e25 : rq.authRoleRevokePermission = !decide (l25 = null) := by
    cases hc : rq.authRoleRevokePermission <;> simp_all
  ihave %h26 := apply.optReqIs_nil l26 rq.clusterVersionSet _ apply.clusterVersionSetIs_nn $$ H26
  have e26 : rq.clusterVersionSet.isSome = !decide (l26 = null) := by
    cases hc : rq.clusterVersionSet <;> simp_all
  ihave %h27 := apply.optReqIs_nil l27 rq.clusterMemberAttrSet _ apply.memberAttrSetIs_nn $$ H27
  have e27 : rq.clusterMemberAttrSet.isSome = !decide (l27 = null) := by
    cases hc : rq.clusterMemberAttrSet <;> simp_all
  ihave %h28 := apply.optReqIs_nil l28 rq.downgradeInfoSet _ apply.downgradeInfoSetIs_nn $$ H28
  have e28 : rq.downgradeInfoSet.isSome = !decide (l28 = null) := by
    cases hc : rq.downgradeInfoSet <;> simp_all
  iunfold apply.presentIs at H29
  icases H29 with %h29
  have e29 : rq.downgradeVersionTest = !decide (l29 = null) := by
    cases hc : rq.downgradeVersionTest <;> simp_all
  wp_auto
  repeat' wp_if_destruct
  all_goals (try wp_auto)
  all_goals (
    simp only [reqTypeName, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29] at hn
    clear e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
    simp only [@eq_comm Bool true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.not_eq_false', decide_eq_true_eq, Classical.not_not, Bool.not_eq_eq_eq_not, Bool.not_true] at *
    simp [*] at hn
    subst hn
    iapply HΦ
    itrivial)

end proof

end EtcdGrove
end Perennial
