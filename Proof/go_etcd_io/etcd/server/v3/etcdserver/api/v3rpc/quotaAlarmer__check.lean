/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaAlarmer__check
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Alarm

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.quotaAlarmer.check.wp_proof
    (wp_Alarm : EtcdServer.Alarm.spec (GF := GF) (hG := hG)) :
    v3rpc.quotaAlarmer.check.spec (GF := GF) (hG := hG) := by
  intro qa s E ρ ci cd r rt hrt
  wp_start as ⟨#Hqa, #Hsrv, #HNR, Hlt, Hard, #Hctx⟩
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, #Hiv, -, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.interceptorVars at Hiv
  icases Hiv with ⟨#HeNS, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeNS
  icases HeNS with ⟨%eNS, #HeNS⟩
  iunfold v3rpc.quotaAlarmerAt at Hqa
  icases Hqa with ⟨%qv, %id, #Hq, #Hiq, #Ha, #Hid⟩
  iunfold apply.isQuota at Hiq
  icases Hiq with ⟨%qi, %Hqi, #HAv, -⟩
  subst Hqi
  wp_auto
  wp_apply HAv $$ %rt %r as %b -
  · ipureintro; exact hrt
  cases b
  · wp_auto
    ihave Hu := HNR
    imod Hu with Hid'
    wp_apply wp_Alarm s E ρ ci cd $$ [Hlt Hard Hid' «$r0»] as %resp %err ⟨Hlt, Hard⟩
    · iframe; iframe #
    iapply HΦ
    iframe
  · wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
