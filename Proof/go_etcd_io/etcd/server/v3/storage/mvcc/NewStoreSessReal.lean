/-
**B3: the session contract of a real backend with nothing registered** (`NewStoreSess.lean`):
`storeBackendT_of_backendC`'s construction without its last step (the registration's
`isKeyBackendG_congrDel` to the store's `delKey γ`), at the backend's own deletable keys `bkDel`. It
needs neither `storeDlReg` nor `dlInit`, so the registration stays unfixed through `NewStore`'s batch
session.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreSess

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode backend

section sess
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The session contract of a compacting real backend, unregistered**: as
`storeBackendT_of_backendC` without `storeDlReg`, at `Del := bkDel d.γB`. -/
theorem storeSessT_of_backendC
    (hCRT : backend.backend.ConcurrentReadTx.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hSz : backend.backend.Size.spec (GF := GF) (hG := hG))
    (hSzU : backend.backend.SizeInUse.spec (GF := GF) (hG := hG))
    (hcRL : backend.concurrentReadTx.RLock.spec (GF := GF) (hG := hG))
    (hcRU : backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hcUR : backend.concurrentReadTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hSP : backend.batchTxBuffered.UnsafeSeqPut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hbUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hLSR : backend.backend.LockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUSR : backend.backend.UnlockForSafeRangeDelete.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (d : KBReal) (hP : bridgeParams d.P) (Pk : IProp GF) (γb : GName) (γi : IdxNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized d.γB d.P d.be ∗
        fkV d.γB true ⊢
      ∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeSessT
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) s γ Pk := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsz, #Hfv⟩ %s %γ %hγ
  obtain ⟨-, hk, hi⟩ := hγ
  have hv : bucketView (GF := GF) γ = bkView d.γB := by
    funext q m; unfold bucketView kbView; rw [hk]
  have hrt : storeRT (GF := GF) γ = bkRTx d.γB d.P d.be := by
    unfold storeRT kbRT bkRTx; rw [hk]
  have hwt : storeWT (GF := GF) γ = wbTok d.γB := by
    unfold storeWT kbWT; rw [hk]
  have hpo : storePutOk γ = keyPutOk := by
    unfold storePutOk kbPutOk; rw [hk]
  have hw : storeW (GF := GF) s γ = lateW d.gx := by
    unfold storeW; rw [hk]
  have hhf : hookFn (GF := GF) γ = bkHookIs d.γB := by
    funext g; unfold hookFn kbHookIs; rw [hk]
  have hrq : storeReq (GF := GF) γ = bkReq d.γB d.P d.be := by
    unfold storeReq kbReq; rw [hk]
  have hrb : storeRb (GF := GF) γ = fun r => iprop(rbPart d.γB (· = leaseName) r ∗ ⌜leaseParams d.P⌝) := by
    unfold storeRb kbRb; rw [hk]
  have hbt : storeBt (GF := GF) γ = bkBt d.be := by
    unfold storeBt kbBt; rw [hk]
  have hsr : kbSR (GF := GF) γ.kb = srSlot d.be := by unfold kbSR; rw [hk]
  have hsrh : kbSRh (GF := GF) γ.kb = srHeld d.be := by unfold kbSRh; rw [hk]
  have hmw : kbMWv (GF := GF) γ.kb γ.bucket = bkMW d.γB := by unfold kbMWv; rw [hk]
  have hnc : kbNoCmpF (GF := GF) γ.kb γ.bucket = bkNoCmpF d.γB := by unfold kbNoCmpF; rw [hk]
  have hwi : kbWi (GF := GF) γ.kb = lateW d.gx := by unfold kbWi; rw [hk]
  have hhn : kbHookNilAt (GF := GF) γ.kb = fun dq => plHookAt d.γB dq func.nil := by
    funext dq; unfold kbHookNilAt; rw [hk]
  iunfold mvcc.storeSessT
  iexists bkDel d.γB
  rw [hv, hrt, hwt, hpo, hw, hhf, hrq, hrb, hbt, hsr, hsrh, hmw, hnc, hwi, hhn]
  iapply isKeyBackendG_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
    hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe (storeCmp γ) (fun _ => hLSR) (fun _ => hUSR)
    (fun _ => hUP) hP (fun _ k h => KBReal_P_HK d k h) (fun _ _ => Iff.rfl) d.γB (lateW d.gx) Pk d.be
    $$ [$Hpkg $Hsch $Hb $Hsz]
  iintro !> -; iexact Hfv

end sess

end mvcc
end EtcdGrove
end Perennial
