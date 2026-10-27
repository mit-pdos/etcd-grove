/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3alarm/AlarmStore__Recover.lean`. Lean-first
(no Rocq counterpart); D22 receiver epochs, S7c (2026-10-23).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__Recover

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Assumptions]

instance (priority := high) alarmStore_typeRepr_u' :
    TypeRepr v3alarm.AlarmStore.underlying v3alarm.AlarmStore :=
  go.type_repr_underlying (u := v3alarm.AlarmStore.underlying)

theorem v3alarm.AlarmStore.Recover.wp_proof
    (hR : v3alarm.AlarmStore.restore.spec (GF := GF) (hG := hG)) :
    v3alarm.AlarmStore.Recover.spec (GF := GF) (hG := hG) := by
  intro a be0 abl lg be γB P W Pk qo r
  wp_start as ⟨#Ha, Hon, #Hbb, #Hbl, %Hlgnn, #HB, Ho, Hwb, Hrb, %Hr⟩
  iunfold isAlarmStore at Ha
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Ha] as ⟨Hlocked, HR⟩
  iunfold alarmLockInv at HR
  icases HR with ⟨%tm, %gm, %ab, Htypes, Hm, Hin, Hbe⟩
  iunfold alarmBeOn at Hon
  icases Hon with ⟨%abl0, %lg0, %Hlg0, Hbe', #Hb0, #Hl0⟩
  icombine Hbe Hbe' gives %Hab
  subst Hab
  ihave Hbe : alarmBeAddr a ↦ alarmBkIface abl0 $$ [Hbe Hbe']
  · have h := ((typedPointsto_dfractional (GF := GF) (alarmBeAddr a) (alarmBkIface abl0)).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)).2
    rw [DFrac.op_own, Qp.half_add_half] at h
    iapply h
    iframe Hbe Hbe'
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w32) (V := GoMap)
    go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType.ty v3alarm.alarmSet.ty) as %tm' Hm'
  (try wp_auto)
  wp_apply hR a abl lg be (DFrac.own 1) γB P W Pk qo r tm' ∅
    $$ [Hbe Htypes Hm' Ho Hwb Hrb] as %err ⟨%Herr, Hbe, Htypes, Hm', Ho, Hrb⟩
  · iframe #; iframe Hbe Htypes Hm' Ho Hwb Hrb
    ipureintro; exact ⟨Hlgnn, Hr⟩
  icases ((typedPointsto_dfractional (GF := GF) (alarmBeAddr a) (alarmBkIface abl)).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)).1 $$ [Hbe] with ⟨Hbe, Hbe'⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hbe
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Ha $Hlocked Htypes Hm' Hbe]
  · inext
    iunfold alarmLockInv
    iexists tm', ∅, alarmBkIface abl
    iframe Htypes Hm' Hbe
    iapply BigSepM.bigSepM_empty.2
    itrivial
  (try wp_auto)
  iapply HΦ
  iframe Ho Hrb
  isplitr
  · ipureintro; exact Herr
  iunfold alarmBeOn
  iexists abl, lg
  iframe Hbe' Hbb Hbl
  ipureintro; exact Hlgnn

end proof

end EtcdGrove
end Perennial
