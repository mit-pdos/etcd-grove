/-
Proof of the spec of the same name (k8s 7f-4). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newCancellableContext

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.newCancellableContext.wp_proof :
    v3rpc.newCancellableContext.spec (GF := GF) (hG := hG) := by
  intro parent cd
  wp_start as ⟨#Hctx, %Hb⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, #Hiv, -, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.interceptorVars at Hiv
  icases Hiv with ⟨-, -, -, -, #HeNoL, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeNoL
  icases HeNoL with ⟨%e, #He, -⟩
  wp_auto
  iapply wp_fupd
  wp_apply v3rpc.wp_WithCancel_cancelCtx parent cd $$ [] as %c %γ' %cancel
    ⟨#Hcancel, #Hc1, #Hfrom, #Hf, #Hcc⟩
  · iframe #
  irename : («$r0_ptr» ↦ (_ : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext) :
    IProp GF) => Hcc0
  iStructNamed Hcc0
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  imod (sync.init_RWMutex_threadPoolL (v3rpc.ccReasonP «$r0_ptr» (GoInterface.ok e)) (E := ⊤) v3rpc.ccPoolN
    v3rpc.ctxErrLvl (v3rpc.ccLockF «$r0_ptr») Hb) $$ [cancelReason] lock with ⟨%γp, #Hguard, #Hpool⟩
  · inext
    iunfold v3rpc.ccReasonP
    iexists ⟨GoInterface.nil, Or.inl rfl⟩
    iexact cancelReason
  ipersist Context
  ipersist cancel
  imodintro
  iapply HΦ
  iframe #
  iunfold v3rpc.ccHandle
  iexists c, γ', cancel, e, γp
  iframe #
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  iunfold noLeaderErr
  iexists e
  iframe #
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
