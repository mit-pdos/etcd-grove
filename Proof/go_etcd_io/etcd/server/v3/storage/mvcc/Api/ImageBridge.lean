/-
**The storage at an image, as the internal constructors take it** (B3, mvccfull's Freeze,
2026-11-10; review round 2's S3/S4, `notes/review/mvccfull-f1-r2.md`). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

* `newStore_of_storage`: from `mvccStorageFor B Pk L c u`, what the internal `NewStore.spec`/`New.spec`
  take of the backend, at the image's records `r` (compaction revision `c`, resumed iff `u`) and
  `L = [[], []] ++ R`, at any store names over the storage's instance, a bucket `γb` and index
  names `γi`: the session contract, the contract behind the fix, the clean read, the image, the
  receipt, the registration, the tokens. `RestoreApi.lean`'s private `restore_of_storage` at any
  names (its body, with the session contract and the two write tokens; that lemma is unchanged).
* `imgFkWfD`, `imgFkV`, `imgRdToks`: copies of `RestoreApi.lean`'s `fkWfD_of_keyImageM`,
  `fkV_of_fkCl` and `NewStoreApi.lean`'s `bkRTx_of_rdToks` (this module is below both).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendRecsSnap
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreImageOpen
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreMoves
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStoreSessReal

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

/-- The image's compaction keys are well formed (`fkWfD_of_keyImageM`'s copy). -/
theorem imgFkWfD (d' : KBReal) (L : Log) (r : CmpRecs) (D : backend.Data)
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

/-- The compaction keys' flag's value, from the open's well-formed keys (`fkV_of_fkCl`'s copy). -/
theorem imgFkV (γB : backend.BNames) (P : backend.BParams) (D : backend.Data)
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

/-- Each reader slot's token with the reader's share of the open token (`bkRTx_of_rdToks`'s copy). -/
theorem imgRdToks (γ : backend.BNames) (P : backend.BParams) (b : Loc) : ∀ n : Nat,
    ([∗list] _x ∈ List.replicate n (), backend.rdTok (GF := GF) γ P b) ∗
      ([∗list] _x ∈ List.replicate n (), backend.bOpen γ backend.rdOpen) ⊢
      [∗list] _x ∈ List.replicate n (), bkRTx γ P b
  | 0 => by
    simp only [List.replicate]
    iintro -
    iapply BigSepL.bigSepL_nil.2; itrivial
  | n + 1 => by
    simp only [List.replicate]
    iintro ⟨Hr, Ho⟩
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr1, Hr⟩
    icases BigSepL.bigSepL_cons.1 $$ Ho with ⟨Ho1, Ho⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr1 Ho1]
    · unfold bkRTx; iframe Hr1 Ho1
    iapply imgRdToks γ P b n
    iframe Hr Ho

/-- **The storage at an image, as the internal `NewStore`/`New` take it** (`restore_of_storage`'s
body at any store names `γ` over the instance, the bucket `γb` and the index names `γi`): the
image's records `r` (compaction revision `c`, resumed iff `u`), `L = [[], []] ++ R`, the receipts,
the session contract, the contract behind the fix, the clean read lent the reader's token and the
unfixed registration, the image, `kbNoDelOff`, the registration right, the unfixed registration,
the two write tokens, the safe-range slot, the write-back supply, the reader tokens, and the
backend's opened facts. -/
theorem newStore_of_storage
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
    (hrb : receiptBound GF ≤ 2 ^ 48) (B : MvccStorage) (Pk : IProp GF) (L : Log) (c : Int) (u : Bool) (γb : GName)
    (γi : IdxNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      mvccStorageFor B Pk L c u ⊢
    ∃ (d' : KBReal) (r : CmpRecs) (R : Log),
      ⌜etcdStorage d' = B ∧ d'.cm = true ∧ L = [[], []] ++ R ∧ restoreLogOk R ∧
        r.crev = c ∧ r.resumes = u ∧ leaseParams d'.P ∧ recsOk L r⌝ ∗
      restoreRcptM d' L ∗ ⧖ (logCh L) ∗
      (∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d' ∧ γ.idx = γi⌝ →
        storeSessT (storageVal B) s γ Pk) ∗
      (∀ (s : Loc) (γ : StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d' ∧ γ.idx = γi⌝ →
        restoreFixM d' γ -∗ storeBackendTR (storageVal B) s γ Pk r) ∗
      (∀ γ : StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d' ∧ γ.idx = γi⌝ →
        keyCleanReadR (storageVal B) (bucketViewC γ) iprop(storeRT γ ∗ restoreRegM d')
          (kbRecs γ.kb γ.bucket r) r) ∗
      restoreImageM d' γb L r ∗ kbNoDelOff (some d') ∗ kbRegRight (some d') ∗
      restoreRegM d' ∗ kbWT (some d') ∗ kbWT (some d') ∗ kbSRM (some d') ∗
      kbWTSupplyM (some d') ∗
      ([∗list] _x ∈ List.replicate nReaders (), kbRT (some d')) ∗
      □ backend.isBackend d'.γB d'.P (lateW d'.gx) Pk d'.be ∗
      □ (⧗ 1 ={⊤}=∗ backend.wbTok d'.γB) := by
  iintro ⟨#Hbpkg, #Hsch, Hfor⟩
  iunfold mvccStorageFor at Hfor
  icases Hfor with ⟨%bk, %D, %Hf, #Hrc, #Hb, #Hsz, Hv, Hdl, Hfk, Hsr, Hrs, Hrg, Hw1, Hw2, #Hsup,
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
  have hwfD := imgFkWfD bk ([[], []] ++ R) r D hkim
  icases imgFkV bk.γB bk.P D hwfD $$ Hfk with ⟨Hfk, #Hfv⟩
  ihave Himg := restoreImageM_of_openOn bk γb ([[], []] ++ R) r D hcm hP hkim $$ [Hv Hfk]
  · iframe Hv Hfk
  ihave #Hsz1 := Hsz $$ %bk.γB %bk.be
  ihave #Hkc := keyCleanRead_of_backendC hRT hrRL hrRU hrUR hID hName hSafe bk hP Pk γb r hsign
    $$ [$Hbpkg $Hsch $Hb $Hsz1]
  ihave #Hsess := storeSessT_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
    hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP bk hP Pk γb γi
    $$ [$Hbpkg $Hsch $Hb $Hsz1 $Hfv]
  ihave Hrts := imgRdToks bk.γB bk.P bk.be nReaders $$ [Hrs Hopen]
  · iframe Hrs Hopen
  rw [show (storageVal bk : GoInterface) = interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #bk.be from rfl]
  iexists bk, r, R
  isplitr
  · ipureintro; exact ⟨rfl, hcm, rfl, hlok, hrc, hru, hlp, hok⟩
  isplitr
  · unfold restoreRcptM; simp only [hcm, ↓reduceIte]; iexact Hrc
  iframe Hrc Hsess
  isplitr
  · iintro %s %γ %hγ
    have hfx : restoreFixM (GF := GF) bk γ = storeDlReg bk.γB γi := by
      unfold restoreFixM; simp [hcm, hγ.2.2]
    rw [hfx]
    iintro Hfix
    ihave HbkTR := storeBackendTR_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
      hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP bk hP Pk γb γi r hsign
      $$ [$Hbpkg $Hsch $Hb $Hsz1 $Hfix $Hfv]
    iapply HbkTR $$ %s %γ
    ipureintro; exact hγ
  isplitr
  · iintro %γ %hγ
    ihave Hk := Hkc $$ %γ %(And.intro hγ.1 hγ.2.1)
    unfold restoreRegM
    simp only [hcm, ↓reduceIte, hγ.2.1, kbRecs_some]
    iexact Hk
  iframe Himg
  isplitr
  · unfold kbNoDelOff; simp only [kbCmpM, hcm, ↓reduceIte]; itrivial
  isplitl [Hrg]
  · simp only [kbRegRight]; iexact Hrg
  isplitl [Hdl]
  · unfold restoreRegM; simp only [hcm, ↓reduceIte]; iexact Hdl
  isplitl [Hw1]
  · simp only [kbWT]; iexact Hw1
  isplitl [Hw2]
  · simp only [kbWT]; iexact Hw2
  isplitl [Hsr]
  · unfold kbSRM; simp only [kbCmpM, hcm, kbSR, ↓reduceIte]; iexact Hsr
  isplitr
  · simp only [kbWTSupplyM, kbCmpM, hcm, kbWTSupply, ↓reduceIte]; iexact Hsup
  isplitl [Hrts]
  · have hkrt : kbRT (GF := GF) (some bk) = bkRTx bk.γB bk.P bk.be := by unfold kbRT bkRTx; rfl
    rw [hkrt]; iexact Hrts
  iframe Hb Hsup

/-- **The resumed compaction's context, from the API's** (the API constructors' `if u then …`, as
`watchableStore.Restore.wp_api` builds it): none; the hook unset (the caller's view shift); the hook
set and frozen (the caller's triple). Back: the hook's share, `Post` and `Y` when resumed. -/
theorem resumeCtx_of_api (d' : KBReal) (r : CmpRecs) (u : Bool) (hru : r.resumes = u)
    (Pk : IProp GF) (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF) :
    □ backend.isBackend d'.γB d'.P (lateW d'.gx) Pk d'.be ∗
      (if u then iprop(storageHook (etcdStorage d') dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
        Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗
        storageReq (etcdStorage d') Pk X Y)
       else iprop(True)) ⊢
    ∃ (hkH : Option val) (dqh : DFrac) (PreH QH PostH XH YH : IProp GF),
      resumeCtxM d' r Pk hkH PreH QH PostH dqh XH YH ∗
      (resumeBackM d' r hkH dqh PostH YH -∗
        if u then iprop(storageHook (etcdStorage d') dq f ∗ Post ∗ Y) else iprop(True)) := by
  unfold etcdStorage
  iintro ⟨#Hbk', Hif⟩
  cases hu : u
  · iexists none, dq, iprop(True), iprop(True), iprop(True), iprop(True), iprop(True)
    rw [resumeCtxM_no _ _ _ _ _ _ _ _ _ _ (by rw [hru, hu]),
      resumeBackM_no _ _ _ _ _ _ (by rw [hru, hu])]
    isplitr
    · itrivial
    iintro -
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  have hres : r.resumes = true := by rw [hru, hu]
  simp only [↓reduceIte]
  icases Hif with ⟨Hhook, %Hfdq, HPre, Hrun, Hupd, HX, Hreq⟩
  ihave #Hreq : backend.commitReq (GF := GF) d'.γB d'.P Pk d'.be X Y $$ [Hreq]
  · iunfold storageReq at Hreq; iexact Hreq
  ihave #HreqK : kbReq (GF := GF) (some d') X Y $$ []
  · simp only [kbReq]
    iunfold bkReq
    iright
    iexists (lateW d'.gx), Pk
    iframe Hbk'
    iexact Hreq
  by_cases hf : f = func.nil
  · subst hf
    iexists none, dq, Pre, Q', Post, X, Y
    unfold resumeCtxM resumeBackM
    simp only [hres, ↓reduceIte]
    iunfold hookRun at Hrun
    simp only [↓reduceIte] at *
    isplitl [HX Hhook HPre Hrun Hupd]
    · iframe HX HreqK HPre
      isplitl [Hhook]
      · simp only [kbHookNilAt]; iunfold storageHook at Hhook; iexact Hhook
      iintro HPP
      imod Hrun $$ HPP with HQ'
      iapply Hupd $$ HQ'
    · iintro ⟨HPost, HY, Hnil⟩
      iframe HPost HY
      simp only [kbHookNilAt]
      iunfold storageHook
      iexact Hnil
  · have hdq : dq = DFrac.discard := by
      rcases Hfdq with h | h
      · exact absurd h hf
      · exact h
    subst hdq
    iunfold storageHook at Hhook
    ihave #Hhk : backend.plHookRO (GF := GF) d'.γB f $$ [Hhook]
    · iexact Hhook
    iexists (some #f), DFrac.discard, Pre, Q', Post, X, Y
    unfold resumeCtxM resumeBackM
    simp only [hres, ↓reduceIte]
    iunfold hookRun at Hrun
    simp only [hf, ↓reduceIte]
    isplitl [HX HPre Hrun Hupd]
    · iframe HX HreqK
      isplitr
      · iunfold bkHookIs
        iexists f
        isplitr
        · ipureintro; exact ⟨rfl, hf⟩
        iexact Hhk
      iunfold csContract
      iframe HPre Hrun Hupd
    · iintro ⟨HPost, HY, -⟩
      iframe HPost HY
      iunfold storageHook
      iexact Hhk

end proof

end api
end mvcc
end EtcdGrove
end Perennial
