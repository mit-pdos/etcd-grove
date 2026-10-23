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
  wp_start as ⟨#Hb, ⟨⟨%am, #Hr⟩, HRW⟩, Hpre, Hwt⟩
  ihave Hai : (applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨⟨%gv, #Hgv, %Hgvl⟩, -⟩
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
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
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
      isplitl; rotate_left
      · first | iexact HeI | iapply applyErrIs_nil
      iunfold apply.mPost
      iframe
      iright
      iapply apply.csContract_pre
      iexact Hcs
    iunfold apply.kvOwn at Hkv
    icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
    icases Hard with ⟨Hard, Hwo⟩
    icases mvcc.writerOwn_rt _ $$ Hwo with ⟨Hrt, Hrdb⟩
    wp_apply HAct $$ %am.memberID %am.alarm %Pre %Q %Post [$Hcs $HRW $Hwt $Hrt] as %m ⟨HPP, Hrt, Hm, HRW⟩
    · ipureintro; exact Hif
    ihave Hwo := Hrdb $$ Hrt
    ihave Hkv : apply.kvOwn E log $$ [Hrd Hsw Hknown Hard Hwo]
    · iunfold apply.kvOwn; iframe
    wp_if_destruct
    · -- no alarm member
      iapply HΦ
      isplitl; rotate_left
      · first | iexact HeI | iapply applyErrIs_nil
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
    wp_apply hID as %s1 %Hs1
    wp_apply hAT $$ [$Hma] as %s2 ⟨-, %Hs2⟩
    wp_apply wp_slice_literal (l := [s1, s2])
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply hWLV gv _ [go!"server_id", go!"alarm_type"] _ _ $$ [Hlsl] as %g ⟨%gi, %Hg, #Hgs, -⟩
    · iframe #; iframe Hlsl; ipureintro
      exact ⟨Hgvl, prometheus.labelValuesOk_two _ _ _ _ (utf8Valid_of_ascii _ Hs1)
        (utf8Valid_of_ascii _ Hs2)⟩
    subst Hg
    iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hgs
    icases Hgs with ⟨#HInc, -⟩
    wp_auto
    wp_apply HInc
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost
    iframe
  wp_if_destruct
  · -- DEACTIVATE
    iunfold apply.kvOwn at Hkv
    icases Hkv with ⟨Hrd, Hsw, Hknown, Hard⟩
    icases Hard with ⟨Hard, Hwo⟩
    icases mvcc.writerOwn_rt _ $$ Hwo with ⟨Hrt, Hrdb⟩
    wp_apply HDeact $$ %am.memberID %am.alarm %Pre %Q %Post [$Hcs $HRW $Hwt $Hrt] as %m ⟨HPP, Hrt, Hm, HRW⟩
    ihave Hwo := Hrdb $$ Hrt
    ihave Hkv : apply.kvOwn E log $$ [Hrd Hsw Hknown Hard Hwo]
    · iunfold apply.kvOwn; iframe
    wp_if_destruct
    · -- no alarm member
      iapply HΦ
      isplitl; rotate_left
      · first | iexact HeI | iapply applyErrIs_nil
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
    wp_apply hID as %s1 %Hs1
    wp_apply hAT $$ [$Hma] as %s2 ⟨-, %Hs2⟩
    wp_apply wp_slice_literal (l := [s1, s2])
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply hWLV gv _ [go!"server_id", go!"alarm_type"] _ _ $$ [Hlsl] as %g ⟨%gi, %Hg, #Hgs, -⟩
    · iframe #; iframe Hlsl; ipureintro
      exact ⟨Hgvl, prometheus.labelValuesOk_two _ _ _ _ (utf8Valid_of_ascii _ Hs1)
        (utf8Valid_of_ascii _ Hs2)⟩
    subst Hg
    iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hgs
    icases Hgs with ⟨-, #HDec, -⟩
    wp_auto
    wp_apply HDec
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost
    iframe
  · -- any other action
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost
    iframe
    iright
    iapply apply.csContract_pre
    iexact Hcs

end proof

end EtcdGrove
end Perennial
