/-
**`KV.Restore.contract`** (2026-11-06). Lean-first (no Rocq counterpart). Over the sealed
definitions of `Api.lean` (imported with `import all`).

* `restore_of_storage`: the bridge from the new storage (`mvccStorageFor B' Pk' L c u`) to what the
  internal `store.Restore` takes of the new backend, at the image's records `r` (`imageOk`: their
  compaction revision `c`, resumed iff `u`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.NewStoreApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RestoreCbAu
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendRecsSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreMoves

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- The image's compaction keys are well formed (its records are revisions past `0`). -/
theorem fkWfD_of_keyImageM (d' : KBReal) (L : Log) (r : CmpRecs) (D : backend.Data)
    (h : keyImageM true L r D) : backend.fkWfD d'.P D := by
  unfold keyImageM at h
  simp only [↓reduceIte] at h
  obtain ⟨ents, hk, hfin, hsched, hok, hpos, hcut⟩ := h
  have hfin' : backend.dget D go!"meta" go!"finishedCompactRev" = recBytes r.fin := hfin
  have hsched' : backend.dget D go!"meta" go!"scheduledCompactRev" = recBytes r.sched := hsched
  intro n k v hk' hv
  obtain ⟨rfl, hk'⟩ := hk'
  show metaRevVal v
  rcases hk' with rfl | rfl
  · rw [hsched'] at hv; exact recBytes_metaRevVal hpos.2 hv
  · rw [hfin'] at hv; exact recBytes_metaRevVal hpos.1 hv

/-- The compaction keys' flag's value, from the open's well-formed keys (persistent). -/
theorem fkV_of_fkCl (γB : backend.BNames) (P : backend.BParams) (D : backend.Data)
    (hwf : backend.fkWfD P D) :
    backend.fkCl (GF := GF) γB P D ⊢ backend.fkCl γB P D ∗ backend.fkV γB true := by
  unfold backend.fkCl
  rw [backend.fkWInit_of_wf hwf]
  iintro ⟨Ho, Hd, Hx, #Hvr⟩
  iframe Ho Hd Hx Hvr
  unfold backend.fkV
  iunfold backend.fkVR at Hvr
  iexists _, _
  iexact Hvr

/-- **The new storage, as `store.Restore` takes it** (`KV.Restore.contract`'s `mvccStorageFor`): at
the image's records `r` (compaction revision `c`, resumed iff `u`) and some restored log
`L = [[], []] ++ R`, the restored log's receipt, the new backend's contract at the records at any
names over it (the deletable keys' registration given), its clean read lent the reader's token and
the unfixed registration, the image, the registration right, the safe-range slot, the write-back
supply, the reader tokens, and the new backend's opened facts. -/
private theorem restore_of_storage
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
    (hrb : receiptBound GF ≤ 2 ^ 48)
    (B' : MvccStorage) (Pk' : IProp GF) (L : Log) (c : Int) (u : Bool) (s : Loc) (γ : StoreNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B' Pk' L c u ⊢
    ∃ (d' : KBReal) (r : CmpRecs) (R : Log),
      ⌜(d' : MvccStorage) = B' ∧ d'.cm = true ∧ L = [[], []] ++ R ∧ restoreLogOk R ∧
        r.crev = c ∧ r.resumes = u ∧ leaseParams d'.P ∧ recsOk L r⌝ ∗
      restoreRcptM d' L ∗ ⧖ (logCh L) ∗
      (∀ p : PhysNames, ⌜p.bucket = γ.bucket ∧ p.kb = some d'⌝ →
        restoreFixM d' (γ.withPhys p) -∗ storeBackendTR (storageVal B') s (γ.withPhys p) Pk' r) ∗
      (∀ p : PhysNames, ⌜p.bucket = γ.bucket ∧ p.kb = some d'⌝ →
        keyCleanReadR (storageVal B') (bucketViewC (γ.withPhys p))
          iprop(storeRT (γ.withPhys p) ∗ restoreRegM d')
          (kbRecs (γ.withPhys p).kb (γ.withPhys p).bucket r) r) ∗
      restoreImageM d' γ.bucket L r ∗ kbNoDelOff (some d') ∗ kbRegRight (some d') ∗
      restoreRegM d' ∗ kbSRM (some d') ∗ kbWTSupplyM (some d') ∗
      ([∗list] _x ∈ List.replicate nReaders (), kbRT (some d')) ∗
      □ backend.isBackend d'.γB d'.P (lateW d'.gx) Pk' d'.be ∗
      □ (⧗ 1 ={⊤}=∗ backend.wbTok d'.γB) := by
  iintro ⟨#Hbpkg, #Hsch, Hfor⟩
  iunfold mvccStorageFor at Hfor
  icases Hfor with ⟨%bk, %D, %Hf, #Hrc, #Hb, #Hsz, Hv, Hdl, Hfk, Hsr, Hrs, Hrg, -, -, #Hsup,
    Hopen⟩
  obtain ⟨hB, hP, hcm, himg, hlp⟩ := Hf
  subst hB
  obtain ⟨r, hkim, hrc, hru, -⟩ := snap.imageOk_keyImageM himg
  have hkim' := hkim
  unfold keyImageM at hkim'
  simp only [↓reduceIte] at hkim'
  obtain ⟨ents, -, -, -, hok, hpos, hcut⟩ := hkim'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, hwf', R, hR, hRne⟩ := himg
  subst hR
  ihave %Hlt := preceipt_lt _ $$ Hrc
  have hch := restoreLog_ch R hRne
  have hidx : IdxWf ([[], []] ++ R) [] :=
    ⟨hwf'.append_nil (by simp), by omega, by simp, hb.2⟩
  have hlok : restoreLogOk R := ⟨hRne, hidx⟩
  have hsign : recsSign r := recsOk_sign _ r hok
  have hwfD := fkWfD_of_keyImageM bk ([[], []] ++ R) r D hkim
  icases fkV_of_fkCl bk.γB bk.P D hwfD $$ Hfk with ⟨Hfk, #Hfv⟩
  ihave Himg := restoreImageM_of_openOn bk γ.bucket ([[], []] ++ R) r D hcm hP hkim $$ [Hv Hfk]
  · iframe Hv Hfk
  ihave #Hsz1 := Hsz $$ %bk.γB %bk.be
  ihave #Hkc := keyCleanRead_of_backendC hRT hrRL hrRU hrUR hID hName hSafe bk hP Pk' γ.bucket r hsign
    $$ [$Hbpkg $Hsch $Hb $Hsz1]
  ihave Hrts := bkRTx_of_rdToks bk.γB bk.P bk.be nReaders $$ [Hrs Hopen]
  · iframe Hrs Hopen
  rw [show (storageVal bk : GoInterface) = interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #bk.be from rfl]
  iexists bk, r, R
  isplitr
  · ipureintro; exact ⟨rfl, hcm, rfl, hlok, hrc, hru, hlp, hok⟩
  isplitr
  · unfold restoreRcptM; simp only [hcm, ↓reduceIte]; iexact Hrc
  iframe Hrc
  isplitr
  · iintro %p %hp
    have hfx : restoreFixM (GF := GF) bk (γ.withPhys p) = storeDlReg bk.γB (γ.withPhys p).idx := by
      unfold restoreFixM; simp [hcm]
    rw [hfx]
    iintro Hfix
    ihave HbkTR := storeBackendTR_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
      hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP bk hP Pk' γ.bucket
      (γ.withPhys p).idx r hsign $$ [$Hbpkg $Hsch $Hb $Hsz1 $Hfix $Hfv]
    iapply HbkTR $$ %s %(γ.withPhys p)
    ipureintro; exact ⟨hp.1, hp.2, rfl⟩
  isplitr
  · iintro %p %hp
    ihave Hk := Hkc $$ %(γ.withPhys p) %(And.intro hp.1 hp.2)
    unfold restoreRegM
    simp only [hcm, ↓reduceIte, StoreNames.withPhys_kb, hp.2, kbRecs_some]
    iexact Hk
  iframe Himg
  isplitr
  · unfold kbNoDelOff; simp only [kbCmpM, hcm, ↓reduceIte]; itrivial
  isplitl [Hrg]
  · simp only [kbRegRight]; iexact Hrg
  isplitl [Hdl]
  · unfold restoreRegM; simp only [hcm, ↓reduceIte]; iexact Hdl
  isplitl [Hsr]
  · unfold kbSRM; simp only [kbCmpM, hcm, kbSR, ↓reduceIte]; iexact Hsr
  isplitr
  · simp only [kbWTSupplyM, kbCmpM, hcm, kbWTSupply, ↓reduceIte]; iexact Hsup
  isplitl [Hrts]
  · have hkrt : kbRT (GF := GF) (some bk) = bkRTx bk.γB bk.P bk.be := by unfold kbRT bkRTx; rfl
    rw [hkrt]; iexact Hrts
  iframe Hb Hsup

end proof

end api
end mvcc
end EtcdGrove
end Perennial
