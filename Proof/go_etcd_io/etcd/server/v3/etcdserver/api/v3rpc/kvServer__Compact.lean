/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer__Compact
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin__isPermitted
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fill

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.kvServer.Compact.wp_proof
    (hP : v3rpc.AuthAdmin.isPermitted.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG)) :
    v3rpc.kvServer.Compact.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid n aa E ctx cd r Pin Q
  wp_start as ⟨#Hsrv, #Haaf, #Haa, #Hnil, #Hctx, HRD, HPin, #Hin⟩
  ihave #Hsrv' := Hsrv
  iunfold v3rpc.kvServerIs at Hsrv'
  icases Hsrv' with ⟨%Hpn, #Hhdr, #Hkv, #Hn, -⟩
  (try wp_auto)
  wp_apply (hP aa s E ctx cd) $$ [$HRD] as %err ⟨HRD, #Hout⟩
  · iframe #
  ihave #Hout := adminOut_of_adminOutB _ _ _ _ $$ Hout
  iunfold adminOut at Hout
  icases Hout with ⟨#Herr, #Htok⟩
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    wp_apply hTog $$ [] as %e %He
    · iframe #
      iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Herr
    (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold v3rpc.compactOut
    iright
    isplitr
    · ipureintro; exact ⟨rfl, He⟩
    iright; iexact HPin
  · (try wp_auto)
    ispecialize Htok $$ %rfl
    icases Htok with ⟨%ai, #Htk⟩
    iunfold v3rpc.compactOk at Hin
    ispecialize Hin $$ %ai
    wp_apply Hin $$ [$HPin $HRD] as %resp %err2 ⟨HRD, Hans⟩
    · iframe #
    icases Hans with (⟨%Hok, %h, %rv, #Hhf, Hw, Hrev, HQ⟩ | ⟨%Hrn, #Hse, HQ⟩)
    · obtain ⟨He, Hrn⟩ := Hok
      subst He
      (try wp_auto)
      wp_apply hFill $$ [$Hw $Hrev] as ⟨Hf, %rv', Hrev'⟩
      · iframe #
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold v3rpc.compactOut
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, Hrn⟩
      iexists h, rv, rv'
      iframe
      iframe #
    · ihave #Hse' := Hse
      iunfold v3rpc.srvErrIs at Hse'
      icases Hse' with ⟨%Hen, -⟩
      subst Hrn
      cases err2 with
      | nil => exact absurd rfl Hen
      | ok ei =>
        (try wp_auto)
        wp_apply hTog $$ [] as %e %He
        · iframe #
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold v3rpc.compactOut
        iright
        isplitr
        · ipureintro; exact ⟨rfl, He⟩
        ileft; iexact HQ

end proof

end EtcdGrove
end Perennial
