/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthServer__UserGrantRole.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer__UserGrantRole
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.AuthServer.UserGrantRole.wp_proof
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG)) :
    v3rpc.AuthServer.UserGrantRole.spec (GF := GF) (hG := hG) := by
  intro p s ctx r P Q
  wp_start as ⟨#Has, HP, #Hin⟩
  iunfold v3rpc.authServerIs at Has
  icases Has with ⟨%Hpn, #Hauth⟩
  (try wp_auto)
  iunfold v3rpc.authInnerOk at Hin
  wp_apply Hin $$ [$HP] as %resp %err ⟨#Herr, Hout⟩
  iunfold authEntryOut at Hout
  icases Hout with (⟨%He, HQ⟩ | ⟨⟨%Hres, %He⟩, HQ⟩)
  · subst He
    (try wp_auto)
    iapply HΦ
    iunfold v3rpc.authWrapOut
    ileft
    iframe HQ
    ipureintro; rfl
  · subst Hres
    rcases err with ei | _
    · (try wp_auto)
      wp_apply hTog $$ [] as %e %Hne
      · iframe #
        iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Herr
      (try wp_auto)
      iapply HΦ
      iunfold v3rpc.authWrapOut
      iright
      isplitr
      · ipureintro; exact ⟨rfl, Hne⟩
      iexists (GoInterface.ok ei)
      iframe HQ
      ipureintro; exact He
    · exact absurd rfl He

end proof

end EtcdGrove
end Perennial
