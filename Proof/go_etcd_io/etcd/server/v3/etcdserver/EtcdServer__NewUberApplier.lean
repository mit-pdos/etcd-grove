/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__NewUberApplier.lean`. Lean-first (no Rocq
counterpart); placed at the server-construction unit's stage N0 (2026-10-16), unit N1's to prove.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__NewUberApplier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__Get
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.NewUberApplier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.NewUberApplier.wp_proof
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hNU : apply.NewUberApplier.spec (GF := GF) (hG := hG))
    (hGet : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG)) :
    EtcdServer.NewUberApplier.spec (GF := GF) (hG := hG) := by
  intro s lg a cl kv au le ci be fg quota wad RD dq
  wp_start as ⟨#Hlg, #Hkv, #Ha, #Hau, #Hle, #Hcl, #Hci, Hbe, #Hfg, #Hgate, #Hquota, #Hwad,
    #Hal, HRD⟩
  ihave #Hgate' := Hgate
  iunfold isFeatureGate at Hgate'
  icases Hgate' with ⟨%fi, %Hfi, #HEn⟩
  wp_auto
  wp_apply hKV s kv $$ []
  · iframe #
  subst Hfi
  wp_auto
  wp_apply HEn as %b -
  ihave #Hapkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #Hvpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  ihave #HGet : apply.alarmGetOk (GF := GF) a $$ []
  · iunfold apply.alarmGetOk
    iintro !> %at' %Φ' !> - HΦ'
    iapply (hGet a at') $$ [] HΦ'
    iframe #
  wp_apply hNU _ RD $$ [HRD] as %ua ⟨%p, %Hua, Hown⟩
  · iframe HRD
    iframe #
  iapply HΦ
  iframe Hbe
  iexists p, _
  iframe Hown
  ipureintro
  exact ⟨Hua, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
