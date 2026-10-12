/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Alarm
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType__String
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__WithLabelValues
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.BackendLemmas2

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


theorem apply.applierV3backend.Alarm.wp_proof
    (hID : types.ID.String.spec (GF := GF) (hG := hG))
    (hAT : etcdserverpb.AlarmType.String.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.GaugeVec.WithLabelValues.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Alarm.spec (GF := GF) (hG := hG) := by
  intro E p r log Pre Q Post
  wp_start as ⟨#Hb, ⟨%am, #Hr⟩, Hpre⟩
  ihave Hai : (applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨⟨%gv, #Hgv⟩, -⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  iunfold apply.backendIs at Hb
  icases Hb with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨-, -, -, -, -, #Hal, -⟩
  iunfold apply.isAlarmStore at Hal
  icases Hal with ⟨%Halnn, #HGet, #HAct, #HDeact⟩
  iunfold apply.alarmRequestIs at Hr
  icases Hr with ⟨%Hrnn, #Hact, #Halarm, #Hmid⟩
  iStructNamed Hopts
  wp_auto
  iStructNamed «$r0»
  wp_if_destruct
  · -- GET
    wp_apply HGet as %sl -
    iapply HΦ
    iunfold apply.mPost
    iframe
    iright
    iapply apply.csContract_pre
    iexact Hcs
  simp only [etcdserverpb.AlarmRequest_DEACTIVATE,
    etcdserverpb.AlarmType_NONE]
  wp_if_destruct
  · -- ACTIVATE
    wp_if_destruct
    · -- NONE: nothing
      iapply HΦ
      iunfold apply.mPost
      iframe
      iright
      iapply apply.csContract_pre
      iexact Hcs
    wp_apply HAct $$ %am.memberID %am.alarm %Pre %Q %Post [$Hcs] as %m ⟨HPP, Hm⟩
    wp_if_destruct
    · -- no alarm member
      iapply HΦ
      iunfold apply.mPost
      iframe
    icases Hm with (%Hn | #Hm)
    · exact absurd Hn Hif
    iunfold apply.alarmMemberIs at Hm
    icases Hm with ⟨-, %a, #Hma⟩
    ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hcap := ownSliceCap_nil (V := Loc) (GF := GF)
    wp_apply wp_slice_literal (l := [m])
    isplitr
    · ipureintro; rfl
    iintro %msl ⟨Hmsl, -⟩
    wp_auto
    wp_apply (wp_slice_append (V := Loc) slice.nil [] _ [m] (DFrac.own 1)) $$ [$Hmsl] as %sl1 -
    · iframe #
    wp_apply hID as %s1 -
    wp_apply hAT $$ [$Hma] as %s2 -
    wp_apply wp_slice_literal (l := [s1, s2])
    isplitr
    · ipureintro; rfl
    iintro %lsl -
    wp_auto
    wp_apply hWLV as %g ⟨%gi, %Hg, #Hgs⟩
    subst Hg
    iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hgs
    icases Hgs with ⟨#HInc, -⟩
    wp_auto
    wp_apply HInc
    iapply HΦ
    iunfold apply.mPost
    iframe
  wp_if_destruct
  · -- DEACTIVATE
    wp_apply HDeact $$ %am.memberID %am.alarm %Pre %Q %Post [$Hcs] as %m ⟨HPP, Hm⟩
    wp_if_destruct
    · -- no alarm member
      iapply HΦ
      iunfold apply.mPost
      iframe
    icases Hm with (%Hn | #Hm)
    · exact absurd Hn Hif
    iunfold apply.alarmMemberIs at Hm
    icases Hm with ⟨-, %a, #Hma⟩
    ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hcap := ownSliceCap_nil (V := Loc) (GF := GF)
    wp_apply wp_slice_literal (l := [m])
    isplitr
    · ipureintro; rfl
    iintro %msl ⟨Hmsl, -⟩
    wp_auto
    wp_apply (wp_slice_append (V := Loc) slice.nil [] _ [m] (DFrac.own 1)) $$ [$Hmsl] as %sl1 -
    · iframe #
    wp_apply hID as %s1 -
    wp_apply hAT $$ [$Hma] as %s2 -
    wp_apply wp_slice_literal (l := [s1, s2])
    isplitr
    · ipureintro; rfl
    iintro %lsl -
    wp_auto
    wp_apply hWLV as %g ⟨%gi, %Hg, #Hgs⟩
    subst Hg
    iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hgs
    icases Hgs with ⟨-, #HDec, -⟩
    wp_auto
    wp_apply HDec
    iapply HΦ
    iunfold apply.mPost
    iframe
  · -- any other action
    iapply HΦ
    iunfold apply.mPost
    iframe
    iright
    iapply apply.csContract_pre
    iexact Hcs

end proof

end EtcdGrove
end Perennial
