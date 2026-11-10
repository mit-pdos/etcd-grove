/-
**B3: what the callers of the internal chain's corollaries hold** (`NewStoreR.lean`'s
`NewStore.spec_of_specR`, `newWatchableStoreR.lean`'s and `NewR.lean`'s `spec_of_specR`; review round
2's T2, `notes/review/mvccfull-f1-r2.md`). Lean-first (no Rocq counterpart). Scratch with them: not
imported, not linked.

The corollaries take the backend in `specR`'s form: the session contract (`storeSessT`), the contract
behind the fix of the deletable keys' registration (`restoreFixM d γ -∗ storeBackendT`), the clean
read lent `storeRT γ ∗ restoreRegM d`, the unfixed registration `restoreRegM d`, and `kbNoDelOff`.
`backendC_newStoreR_pre` derives exactly these from what their callers hold at the call, in both
modes, from the backend's creator's unfixed registration `dlInit` (kept, on: no `storeDlReg_fix`
before the call):
- `NewStoreApi.lean`'s `NewStore.wp_proof` and `NewApi.lean`'s `New.wp_proof` (on: `fkV … true` from
  `bkNoCmp_fkV_of_fkCl`; today they fix the registration first, `storeDlReg_fix`);
- `StoreBackend.lean`'s `NewStore_backend` (either mode: its premise `□ (⌜d.cm⌝ -∗ fkV …)`; today
  it fixes `dlNoDel` or `storeDlReg` first).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreSessReal
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode backend

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The corollaries' backend premises, from the real backend** (see the file header): the
session contract, the contract behind the fix, the clean read lent the unfixed registration, that
registration and `kbNoDelOff`, for every store of the instance `d` over `γb`, `γi`. -/
theorem backendC_newStoreR_pre
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
    let b : GoInterface :=
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #d.be
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P (lateW d.gx) Pk d.be ∗ keySized d.γB d.P d.be ∗
      backend.dlInit d.γB ∗ □ (⌜d.cm = true⌝ -∗ backend.fkV d.γB true) ⊢ |==> (
      (∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeSessT b s γ Pk) ∗
      (∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.restoreFixM d γ -∗ storeBackendT b s γ Pk) ∗
      (∀ γ : StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        keyCleanRead b (bucketViewC γ) iprop(storeRT γ ∗ mvcc.restoreRegM d)
          (kbNoCmpF γ.kb γ.bucket)) ∗
      mvcc.restoreRegM d ∗ kbNoDelOff (some d)) := by
  intro b
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hsz, Hdl, #Hfv⟩
  cases hc : d.cm with
  | true =>
    ihave #Hfv' := Hfv $$ []
    · ipureintro; rfl
    ihave #Hsess := storeSessT_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
      hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d hP Pk γb γi
      $$ [$Hpkg $Hsch $Hb $Hsz $Hfv']
    ihave #Hcr := keyCleanRead_of_backendC hRT hrRL hrRU hrUR hID hName hSafe d hP Pk γb
      CmpRecs.empty (by simp [recsSign, CmpRecs.empty]) $$ [$Hpkg $Hsch $Hb $Hsz]
    imodintro
    isplitl []
    · iexact Hsess
    isplitl []
    · iintro %s %γ %hγ HFix
      rw [mvcc.restoreFixM, hc] at *
      simp only [↓reduceIte]
      rw [← hγ.2.2]
      iapply storeBackendT_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
        hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP d hP Pk γb γ.idx
        $$ [$Hpkg $Hsch $Hb $Hsz $HFix $Hfv']
      ipureintro; exact ⟨hγ.1, hγ.2.1, rfl⟩
    isplitl []
    · iintro %γ %hγ
      have hγ' : γ.bucket = γb ∧ γ.kb = some d := ⟨hγ.1, hγ.2.1⟩
      ihave #Hk := Hcr $$ %γ %hγ'
      have hnc : kbNoCmpF (GF := GF) γ.kb γ.bucket = bkRecs d.γB CmpRecs.empty := by
        unfold kbNoCmpF bkRecs; rw [hγ.2.1]; simp
      rw [hnc, ← keyCleanReadR_empty, mvcc.restoreRegM, hc]
      simp only [↓reduceIte]
      iexact Hk
    rw [mvcc.restoreRegM, hc]
    simp only [kbNoDelOff, kbCmpM, hc, ↓reduceIte]
    iframe Hdl
  | false =>
    imod backend.dlNoDel_fix d.γB $$ Hdl with #Hnd
    ihave #HbT := storeBackendT_of_backend hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
      hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe d hP hc Pk γb $$ [$Hpkg $Hsch $Hb $Hsz $Hnd]
    ihave #Hcr := keyCleanRead_of_backend hRT hrRL hrRU hrUR hID hName hSafe d hP Pk γb
      $$ [$Hpkg $Hsch $Hb $Hsz $Hnd]
    imodintro
    isplitl []
    · iintro %s %γ %hγ
      iapply mvcc.storeSessT_of_storeBackendT
      iapply HbT
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
    isplitl []
    · iintro %s %γ %hγ -
      iapply HbT
      ipureintro; exact ⟨hγ.1, hγ.2.1⟩
    isplitl []
    · iintro %γ %hγ
      have hγ' : γ.bucket = γb ∧ γ.kb = some d := ⟨hγ.1, hγ.2.1⟩
      ihave #Hk := Hcr $$ %γ %hγ'
      have hfr := keyCleanReadR_frame (GF := GF) b (bucketViewC γ) (storeRT γ)
        (kbNoCmpF γ.kb γ.bucket) CmpRecs.empty (mvcc.restoreRegM d)
      rw [keyCleanReadR_empty, keyCleanReadR_empty] at hfr
      iapply hfr
      iexact Hk
    rw [mvcc.restoreRegM, hc]
    simp only [kbNoDelOff, kbCmpM, kbNoDel, hc, Bool.false_eq_true, ↓reduceIte]
    iframe Hnd

end glue

end mvcc
end EtcdGrove
end Perennial
