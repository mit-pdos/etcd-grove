/-
Proof of the spec of the same name (k8s 7f-4). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext__Err

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

theorem v3rpc.cancellableContext.Err.wp_proof :
    v3rpc.cancellableContext.Err.spec (GF := GF) (hG := hG) := by
  intro l c1 cd b
  wp_start as ⟨#Hh, Htok, #Hb⟩
  iunfold v3rpc.ccHandle at Hh
  icases Hh with ⟨%c, %γ, %cancel, %e, %γp, %Hc1, %Hγ, #Hf, #Hcf, #Hctx, #Hcc, #Hcancel, #HnL,
    #Hguard, #Hpool⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iapply fupd_wp
  imod threadPool.borrowL v3rpc.ccPoolN v3rpc.ctxErrLvl γp
    (sync.ownRWMutex (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e))) ⊤
    (fun _ _ => CoPset.mem_full) $$ [Hpool Htok] with ⟨Hslot, Hloan⟩
  · iframe #; iframe
  imodintro
  iapply wp_fupd
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (sync.RWMutex.wp_RLock (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e)))
    $$ [$Hslot] as ⟨Hlk, HR⟩
  iunfold v3rpc.ccReasonP at HR
  icases HR with ⟨%r, Hr⟩
  obtain ⟨rv, hrv | hrv⟩ := r <;> subst hrv
  · -- no reason stored: the embedded context's `Err()`
    wp_auto
    ihave #Hctx' := Hctx
    iunfold context.isContext at Hctx'
    iunfold context.isContextDef at Hctx'
    icases Hctx' with ⟨-, -, #HErr, -, #HErrDone, -⟩
    cases b
    · ihave #HErrU := HErr $$ %Broadcast.Unknown
      wp_apply HErrU $$ [] as %err - -
      wp_apply (sync.RWMutex.wp_RUnlock (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e)))
        $$ [Hlk Hr] as Hslot
      · iframe #; iframe
        inext
        iunfold v3rpc.ccReasonP
        iexists ⟨GoInterface.nil, Or.inl rfl⟩
        iexact Hr
      (try wp_auto)
      imod threadPool.giveBackL v3rpc.ccPoolN v3rpc.ctxErrLvl γp
        (sync.ownRWMutex (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e))) ⊤
        (fun _ _ => CoPset.mem_full) $$ [Hpool Hloan Hslot] with Htok
      · iframe #; iframe
      imodintro
      iapply HΦ
      iframe Htok
      (try simp only [Bool.false_eq_true, ↓reduceIte])
      itrivial
    · (try simp only [↓reduceIte])
      wp_apply HErrDone $$ [Hb] as %err %Hty #Hce
      · iexact Hb
      wp_apply (sync.RWMutex.wp_RUnlock (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e)))
        $$ [Hlk Hr] as Hslot
      · iframe #; iframe
        inext
        iunfold v3rpc.ccReasonP
        iexists ⟨GoInterface.nil, Or.inl rfl⟩
        iexact Hr
      (try wp_auto)
      imod threadPool.giveBackL v3rpc.ccPoolN v3rpc.ctxErrLvl γp
        (sync.ownRWMutex (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e))) ⊤
        (fun _ _ => CoPset.mem_full) $$ [Hpool Hloan Hslot] with Htok
      · iframe #; iframe
      imodintro
      iapply HΦ
      iframe Htok
      (try simp only [↓reduceIte])
      isplitr
      · ipureintro; exact context.isTypedErr_ne_nil Hty
      ileft; iexact Hce
  · -- `ErrGRPCNoLeader` stored
    wp_auto
    wp_apply (sync.RWMutex.wp_RUnlock (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e)))
      $$ [Hlk Hr] as Hslot
    · iframe #; iframe
      inext
      iunfold v3rpc.ccReasonP
      iexists ⟨GoInterface.ok e, Or.inr rfl⟩
      iexact Hr
    (try wp_auto)
    imod threadPool.giveBackL v3rpc.ccPoolN v3rpc.ctxErrLvl γp
      (sync.ownRWMutex (v3rpc.ccLockF l) (v3rpc.ccReasonP l (GoInterface.ok e))) ⊤
      (fun _ _ => CoPset.mem_full) $$ [Hpool Hloan Hslot] with Htok
    · iframe #; iframe
    imodintro
    iapply HΦ
    iframe Htok
    cases b
    · (try simp only [Bool.false_eq_true, ↓reduceIte])
      itrivial
    · (try simp only [↓reduceIte])
      isplitr
      · ipureintro; simp
      iright; iexact HnL

end proof

end EtcdGrove
end Perennial
