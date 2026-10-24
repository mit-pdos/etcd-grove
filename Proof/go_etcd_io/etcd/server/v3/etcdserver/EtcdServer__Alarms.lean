/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Alarms.lean`. Lean-first (no Rocq
counterpart); verified for `etcd-io/etcd#22654`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Alarms
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__Get

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

theorem EtcdServer.Alarms.wp_proof
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG)) :
    EtcdServer.Alarms.spec (GF := GF) (hG := hG) := by
  intro s a
  wp_start as ⟨#Has, #Halm⟩
  ihave #Palm : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  wp_auto
  wp_apply hAG a _ $$ [$Palm $Halm] as %sl Hsl
  iapply HΦ
  iexact Hsl

/-- Corollary: any concurrent caller holding the persistent server invariant `isServer s γ ci TM E ρ
γr` can call `s.Alarms()` without any lock on `s` (safe concurrently with `applySnapshot`'s in-place
`s.alarmStore.Recover(...)`). -/
theorem EtcdServer.wp_Alarms_isServer
    (hAlarms : EtcdServer.Alarms.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServer s γ ci TM E ρ γr }}
      (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Alarms")) (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ l : List Loc, sl ↦* l ∗ ownSliceCap Loc sl (DFrac.own 1) }} := by
  iintro %Φ ⟨#Hpkg, #Hsrv⟩ HΦ
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, ⟨%fv, #Hfv⟩, -, -, -⟩
  iunfold srvFieldsAt at Hfv
  icases Hfv with ⟨-, -, -, -, -, -, -, -, -, -, #Has, -, -, -, -, -, -, -, -, -, #Halm⟩
  wp_apply hAlarms s fv.alarmStore $$ [$Hpkg $Has $Halm] as %sl Hsl
  iapply HΦ
  iexact Hsl

end proof

end EtcdGrove
end Perennial
