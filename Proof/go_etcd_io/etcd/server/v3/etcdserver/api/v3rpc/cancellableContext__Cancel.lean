/-
Proof of the spec of the same name (k8s 7f-4). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext__Cancel

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

theorem v3rpc.cancellableContext.Cancel.wp_proof :
    v3rpc.cancellableContext.Cancel.spec (GF := GF) (hG := hG) := by
  intro l c1 cd reason
  wp_start as ⟨#Hh, #Hr⟩
  iunfold v3rpc.ccHandle at Hh
  icases Hh with ⟨%c, %γ, %cancel, %e, %γp, %Hc1, %Hγ, #Hf, #Hcf, #Hctx, #Hcc, #Hcancel, #HnL,
    #Hguard, #Hpool⟩
  -- the reason is one the lock's invariant allows
  ihave %Hok : ⌜v3rpc.reasonOk (GoInterface.ok e) reason⌝ $$ []
  · icases Hr with (%Hn | #Hn)
    · ipureintro; exact Or.inl Hn
    · iunfold noLeaderErr at Hn HnL
      icases Hn with ⟨%e1, #He1, %Heq1⟩
      icases HnL with ⟨%e2, #He2, %Heq2⟩
      icombine He1 He2 gives %h
      ipureintro; right; rw [Heq1, Heq2, h]
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (sync.RWMutex.wp_Lock_guard (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e)))
    $$ [] as ⟨Hlk, HR⟩
  · iframe #
  iunfold v3rpc.ccReasonP at HR
  icases HR with ⟨%r, Hr⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_Unlock_guard (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e)))
    $$ [Hlk Hr]
  · iframe #; iframe
    inext
    iunfold v3rpc.ccReasonP
    iexists ⟨reason, Hok⟩
    iexact Hr
  iunfold context.cancelSpec at Hcancel
  wp_apply Hcancel $$ [] as #Hcl
  · imodintro; itrivial
  iapply HΦ
  rw [Hγ]
  iexact Hcl

end proof

end EtcdGrove
end Perennial
