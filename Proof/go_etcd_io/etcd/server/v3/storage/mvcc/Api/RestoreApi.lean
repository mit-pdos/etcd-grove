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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.BasicLaws

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

/-- Reader tokens of a real backend give back its open shares. -/
theorem rep_kbRT_bOpen (d : KBReal) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), kbRT (GF := GF) (some d)) ⊢
      [∗list] _x ∈ List.replicate n (), backend.bOpen d.γB backend.rdOpen := by
  apply BigSepL.bigSepL_mono
  intro _ _ _
  unfold kbRT
  iintro ⟨-, H⟩
  iexact H

/-- **`KV.Restore.contract` at `*watchableStore`** (2026-11-06): the internal
`watchableStore.Restore` at the store's current names (the open token's `p`), over the new
storage (`restore_of_storage`), with the client's update as the takeover's ghost step
(`restoreCb_of_au`) and the resumed compaction's context from the hook's and the commit's. -/
theorem watchableStore.Restore.wp_api
    (hRst : mvcc.watchableStore.Restore.spec (GF := GF) (hG := hG))
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
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG)) :
    watchableStore.Restore.spec (GF := GF) := by
  intro s (γ : StoreNames) B B' Pk Pk' σ' u L dq f Pre Q' Post X Y Q
  iintro %Φ ⟨#Hpkg, Hmv, Htt, Hopen, HB, Hfor, %Hσ', Hhook, %Hfdq, HPre, Hrun, Hupd, HX, #Hreq,
    HLo, %Hlok, HAU⟩ HΦ
  iunfold isMvcc at Hmv
  icases Hmv with #Hmv
  ihave %hrb := isMvcc_rb (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s) γ $$ []
  · iunfold isMvcc; imodintro; iexact Hmv
  icases Hmv with (⟨Hmv, %Hwq⟩ | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s', %Hk, -⟩
    exfalso
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccWatchable at Hmv
  icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, #Hws, -, #Hrp, #Hloc, #Hperm, #Hfree⟩
  obtain ⟨Hk, hγ⟩ := Hk
  rw [interface_mkOk_inj] at Hk
  have hs : s = s' := go.intoVal_inj Hk.2
  subst hs
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  -- the open token, at the inner store's location and current names
  iunfold mvccOpen at Hopen
  icases Hopen with ⟨%s2, %p, %c, #Hloc2, Hright, Hcra, HRT, #Hsup, %hc, Hor, Hwo⟩
  ihave %Hss := locIs_agree _ _ _ $$ [Hloc Hloc2]
  · isplitl
    · iexact Hloc
    · iexact Hloc2
  cases Hss
  -- the backend share: its names are the right's
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  obtain ⟨hpk, hcm, rfl⟩ := Hd
  icases (compactRightR_iff st ((γ : StoreNames).withPhys p) c).1 $$ Hright with
    ⟨Hcr, Hq, %o, ⟨Hfs, #Hsc, Hstc, Htok⟩, #Hstop⟩
  icases fieldShareAt_cur st ((γ : StoreNames).withPhys p) _ o $$ Hfs with ⟨Hcur, Hfsb⟩
  ihave %Hv := curAt_agree ((γ : StoreNames).withPhys p) ((γ : StoreNames).withPhys p')
      rfl _ _ o o' $$ [Hcur Hcur']
  · isplitl [Hcur]
    · iexact Hcur
    · iexact Hcur'
  obtain ⟨-, hp⟩ := Hv
  have hp' : p = p' := hp
  subst hp'
  ihave Hfs := Hfsb $$ Hcur
  ihave Hright : compactRightR (GF := GF) st ((γ : StoreNames).withPhys p) c $$ [Hcr Hq Hfs Hstc Htok]
  · iapply (compactRightR_iff st ((γ : StoreNames).withPhys p) c).2
    iframe Hcr Hq
    iexists o
    iframe Hfs Hsc Hstc Htok Hstop
  -- the new storage
  icases restore_of_storage hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL
      hbUR hCB hDel hID hName hSafe hLSR hUSR hUP hrb B' Pk' σ'.log σ'.crev u st (γ : StoreNames)
      $$ [$Hbpkg $Hspkg $Hfor]
    with ⟨%d', %r, %R, %Hb, #Hrc, #Hrc2, HbkT, HcrT, Himg, #HndO, Hrr, Hreg, Hsr, #Hwts',
      Hrts, #Hbk', #Hsup'⟩
  obtain ⟨hB', hcm', hL, hlok, hrc, hru, hlp', hrec⟩ := Hb
  subst hB'
  -- the resumed compaction's context, by the case: none; the hook unset; the hook frozen
  ihave ⟨%hkH, %dqh, %PreH, %QH, %PostH, %XH, %YH, Hctx, Hback⟩ :
      ∃ (hkH : Option val) (dqh : DFrac) (PreH QH PostH XH YH : IProp GF),
        resumeCtxM d' r Pk' hkH PreH QH PostH dqh XH YH ∗
        (resumeBackM d' r hkH dqh PostH YH -∗
          storageHook (d' : MvccStorage) dq f ∗ (if u = true then iprop(Post ∗ Y) else iprop(Pre ∗ X)))
      $$ [Hhook HPre Hrun Hupd HX]
  · cases hu : u
    · -- no resumed compaction: the context unused, kept
      iexists none, dq, iprop(True), iprop(True), iprop(True), iprop(True), iprop(True)
      rw [resumeCtxM_no _ _ _ _ _ _ _ _ _ _ (by rw [hru, hu]),
        resumeBackM_no _ _ _ _ _ _ (by rw [hru, hu])]
      isplitr
      · itrivial
      iintro -
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hhook HPre HX
    have hres : r.resumes = true := by rw [hru, hu]
    ihave #HreqK : kbReq (GF := GF) (some d') X Y $$ []
    · simp only [kbReq]
      iunfold bkReq
      iright
      iexists (lateW d'.gx), Pk'
      iframe Hbk'
      iunfold storageReq at Hreq
      iexact Hreq
    by_cases hf : f = func.nil
    · -- the hook unset (at any share): the caller's view shift
      subst hf
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
    · -- the hook set, frozen: the caller's triple
      have hdq : dq = DFrac.discard := by
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
  -- the client's update, as the takeover's ghost step
  iunfold mvccState at HAU
  ihave Hcb := restoreCb_of_au γ p σ' Hσ'.2 Hσ'.1 c hc Q $$ [Hcra HAU]
  · iframe Hcra Hrc2 HAU
  rw [← hrc, hL]
  rw [hL] at Hlok
  -- the internal `Restore`, at the store's current names
  have hγw : isWatchableStore (GF := GF) s st { γw with st := (γ : StoreNames).withPhys p } =
      isWatchableStore s st γw := by rw [← hγ]; rfl
  ihave #Hws' : isWatchableStore (GF := GF) s st { γw with st := (γ : StoreNames).withPhys p } $$ []
  · rw [hγw]; iexact Hws
  iapply (hRst s st { γw with st := (γ : StoreNames).withPhys p } (storageVal (d' : MvccStorage)) d'
      γ.bucket Pk' R c r L iprop(crevAuth γ.api (1 : Qp).half.half r.crev ∗ ∃ σ, Q σ)
      hkH dqh PreH QH PostH XH YH hlok)
    $$ [HbkT HcrT Himg Hrr Hreg Hsr Hrts Hctx HLo HF Hcb Hright Hwo Hcur'] [-]
  · simp only []
    have hpk' : ((γ : StoreNames).withPhys p).kb = some d := hpk
    ihave #HpF : crevPermAt (GF := GF) ((γ : StoreNames).withPhys p) r.finRev $$ []
    · iapply crevPermAt_of _ (fun _ => iprop(True))
      isplitl
      · iapply (crevPermIs_cperm (γ : StoreNames) ((γ : StoreNames).withPhys p) rfl
          (fun _ => iprop(True)))
        iexact Hperm
      · iintro !>; itrivial
    ihave #HpC : crevPermAt (GF := GF) ((γ : StoreNames).withPhys p) r.crev $$ []
    · iapply crevPermAt_of _ (fun _ => iprop(True))
      isplitl
      · iapply (crevPermIs_cperm (γ : StoreNames) ((γ : StoreNames).withPhys p) rfl
          (fun _ => iprop(True)))
        iexact Hperm
      · iintro !>; itrivial
    iframe Hpkg Hrc HpF HpC Hws' Himg HndO Hrr Hreg Hsr Hwts' Hrts Hctx Hcb Hwo
    simp only [StoreNames.withPhys_api, StoreNames.withPhys_leases]
    isplitr
    · ipureintro; exact ⟨d, hpk', by rw [hcm', hcm]⟩
    isplitl [Hright]
    · unfold restoreRightM
      simp only [hpk', kbCmpM, hcm, ↓reduceIte]
      iexact Hright
    isplitl [Hcur']
    · iunfold writerFrag; iexists o'; iexact Hcur'
    isplitr
    · iunfold certOk; iright; iright; iunfold certFree at Hfree
      simp only [StoreNames.withPhys_cok]; iexact Hfree
    isplitl [HbkT]
    · iintro %q %hq; simp only [StoreNames.withPhys_withPhys]; iapply HbkT $$ %q %hq
    isplitl [HcrT]
    · iintro %q %hq; simp only [StoreNames.withPhys_withPhys]; iapply HcrT $$ %q %hq
    isplitl [HLo]
    · iunfold mvccLeases at HLo; iexact HLo
    isplitr
    · ipureintro; exact Hlok
    iexact HF
  -- the post: the open token and the backend share at the new names, the old storage's shares
  inext
  simp only [StoreNames.withPhys_withPhys, StoreNames.withPhys_api, StoreNames.withPhys_leases]
  iintro ⟨%p'', %hp'', Hcl, Hfrag, Hwo', #Hhp', #Hreg', HrB, Hjob, Hold, Hnew, HLo, HF, Hcra',
    %σ0, HQ⟩
  icases Hback $$ HrB with ⟨Hhook, Hres⟩
  have hkp'' : ((γ : StoreNames).withPhys p'').kb = some d' := hp''.2
  have hcmp'' : kbCmpM ((γ : StoreNames).withPhys p'').kb := by rw [hkp'']; exact hcm'
  have hj : nJobRd ((γ : StoreNames).withPhys p).kb = 1 := by
    show nJobRd ((γ : StoreNames).withPhys p).kb = 1
    rw [show ((γ : StoreNames).withPhys p).kb = some d from hpk]; simp [nJobRd, hcm]
  iapply HΦ
  iframe Htt Hres Hhook
  isplitl [Hcl Hcra' Hnew Hor Hwo']
  · iunfold mvccOpen
    iexists st, p'', r.crev
    iframe Hloc
    isplitl [Hcl]
    · iapply (storeCloserM_on _ _ _ hcmp'').1; iexact Hcl
    iframe Hcra' Hnew
    isplitr
    · rw [show p''.kb = some d' from hp''.2]; iexact Hwts'
    isplitr
    · ipureintro; exact CmpRecs.crev_ge _ r hrec
    isplitl [Hor]
    · iunfold openRest at Hor
      iunfold openRest
      icases Hor with ⟨-, Hw⟩
      iframe Hw
      ipureintro; show kbCmpM p''.kb; rw [show p''.kb = some d' from hp''.2]; exact hcm'
    iexact Hwo'
  isplitl [HF Hfrag]
  · iunfold mvccBackend
    iframe HF
    iunfold writerFrag at Hfrag
    icases Hfrag with ⟨%o2, Hcur2⟩
    iexists p'', o2, d'
    iframe Hcur2 Hbk'
    isplitr
    · ipureintro; exact ⟨hp''.2, hcm', rfl⟩
    isplitr
    · iintro !>; iexists st; iexact Hreg'
    isplitr
    · iexact Hhp'
    isplitr
    · iintro !> Hlc
      unfold storeWT kbWT
      rw [hkp'']
      iapply Hsup' $$ Hlc
    ipureintro; exact hlp'
  isplitl [Hold Hjob HRT]
  · iunfold storageRest
    rw [hj]
    unfold compactJobResM
    simp only [show kbCmpM ((γ : StoreNames).withPhys p).kb from by
      rw [show ((γ : StoreNames).withPhys p).kb = some d from hpk]; exact hcm, ↓reduceIte]
    icases Hjob with ⟨Hjrt, -⟩
    have h3 : 3 ≤ nReaders := by rw [nReaders_val]; omega
    have hn : nReaders = (nReaders - 1 - 1) + 1 + 1 := by omega
    have hrt : storeRT (GF := GF) ((γ : StoreNames).withPhys p) = kbRT (some d) := by
      unfold storeRT; rw [show ((γ : StoreNames).withPhys p).kb = some d from hpk]
    rw [hrt]
    rw [show ((γ : StoreNames).withPhys p).kb = some d from hpk] at *
    rw [hn, List.replicate_succ, List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    isplitl [HRT]
    · unfold kbRT; icases HRT with ⟨-, H⟩; iexact H
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hjrt]
    · unfold kbRT; icases Hjrt with ⟨-, H⟩; iexact H
    rw [show nReaders - 1 - 1 + 1 + 1 - 1 - 1 = nReaders - 1 - 1 by omega]
    iapply rep_kbRT_bOpen
    iexact Hold
  iunfold mvccLeases
  iframe HLo
  iexists σ0; iexact HQ

/-- **`KV.Restore.contract` at `*store`** (2026-11-06): the internal `store.Restore` at the store's
current names, as for a watchable store (`watchableStore.Restore.wp_api`), with the plain handle's
pieces: the store's certificate at its first log (the internal `L`, which only a watchable store
pins), the fields' quarter and the deposit (the open token's, `openRest`). -/
theorem store.Restore.wp_api
    (hRst : mvcc.store.Restore.spec (GF := GF) (hG := hG))
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
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG)) :
    store.Restore.spec (GF := GF) := by
  intro s (γ : StoreNames) B B' Pk Pk' σ' u L dq f Pre Q' Post X Y Q
  iintro %Φ ⟨#Hpkg, Hmv, Htt, Hopen, HB, Hfor, %Hσ', Hhook, %Hfdq, HPre, Hrun, Hupd, HX, #Hreq,
    HLo, %Hlok, HAU⟩ HΦ
  iunfold isMvcc at Hmv
  icases Hmv with #Hmv
  ihave %hrb := isMvcc_rb (interface.mkOk (go.GoType.PointerType store.ty) #s) γ $$ []
  · iunfold isMvcc; imodintro; iexact Hmv
  icases Hmv with (⟨Hmv, %Hwq⟩ | Hmv)
  rotate_left 1
  · iunfold isMvccWatchable at Hmv
    icases Hmv with ⟨%s', %st, %γw, %γp, %Hk, -⟩
    exfalso
    obtain ⟨Hk, -⟩ := Hk
    rw [interface_mkOk_inj] at Hk
    exact absurd Hk.1 (by simp [watchableStore.ty, store.ty])
  iunfold isMvccPlain at Hmv
  icases Hmv with ⟨%s', %Hk, #Hs, #Hloc, #Hperm, -, #Hfree, #HcL0, -⟩
  have hs : s = s' := mkOk_loc_inj _ Hk
  subst hs
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  -- the open token, at the inner store's location and current names
  iunfold mvccOpen at Hopen
  icases Hopen with ⟨%s2, %p, %c, #Hloc2, Hright, Hcra, HRT, #Hsup, %hc, Hor, Hwo⟩
  ihave %Hss := locIs_agree _ _ _ $$ [Hloc Hloc2]
  · isplitl
    · iexact Hloc
    · iexact Hloc2
  cases Hss
  -- the backend share: its names are the right's
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
  obtain ⟨hpk, hcm, rfl⟩ := Hd
  icases (compactRightR_iff s ((γ : StoreNames).withPhys p) c).1 $$ Hright with
    ⟨Hcr, Hq, %o, ⟨Hfs, #Hsc, Hstc, Htok⟩, #Hstop⟩
  icases fieldShareAt_cur s ((γ : StoreNames).withPhys p) _ o $$ Hfs with ⟨Hcur, Hfsb⟩
  ihave %Hv := curAt_agree ((γ : StoreNames).withPhys p) ((γ : StoreNames).withPhys p')
      rfl _ _ o o' $$ [Hcur Hcur']
  · isplitl [Hcur]
    · iexact Hcur
    · iexact Hcur'
  obtain ⟨-, hp⟩ := Hv
  have hp' : p = p' := hp
  subst hp'
  ihave Hfs := Hfsb $$ Hcur
  ihave Hright : compactRightR (GF := GF) s ((γ : StoreNames).withPhys p) c $$ [Hcr Hq Hfs Hstc Htok]
  · iapply (compactRightR_iff s ((γ : StoreNames).withPhys p) c).2
    iframe Hcr Hq
    iexists o
    iframe Hfs Hsc Hstc Htok Hstop
  -- the new storage
  icases restore_of_storage hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL
      hbUR hCB hDel hID hName hSafe hLSR hUSR hUP hrb B' Pk' σ'.log σ'.crev u s (γ : StoreNames)
      $$ [$Hbpkg $Hspkg $Hfor]
    with ⟨%d', %r, %R, %Hb, #Hrc, #Hrc2, HbkT, HcrT, Himg, #HndO, Hrr, Hreg, Hsr, #Hwts',
      Hrts, #Hbk', #Hsup'⟩
  obtain ⟨hB', hcm', hL, hlok, hrc, hru, hlp', hrec⟩ := Hb
  subst hB'
  -- the resumed compaction's context, by the case: none; the hook unset; the hook frozen
  ihave ⟨%hkH, %dqh, %PreH, %QH, %PostH, %XH, %YH, Hctx, Hback⟩ :
      ∃ (hkH : Option val) (dqh : DFrac) (PreH QH PostH XH YH : IProp GF),
        resumeCtxM d' r Pk' hkH PreH QH PostH dqh XH YH ∗
        (resumeBackM d' r hkH dqh PostH YH -∗
          storageHook (d' : MvccStorage) dq f ∗ (if u = true then iprop(Post ∗ Y) else iprop(Pre ∗ X)))
      $$ [Hhook HPre Hrun Hupd HX]
  · cases hu : u
    · -- no resumed compaction: the context unused, kept
      iexists none, dq, iprop(True), iprop(True), iprop(True), iprop(True), iprop(True)
      rw [resumeCtxM_no _ _ _ _ _ _ _ _ _ _ (by rw [hru, hu]),
        resumeBackM_no _ _ _ _ _ _ (by rw [hru, hu])]
      isplitr
      · itrivial
      iintro -
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hhook HPre HX
    have hres : r.resumes = true := by rw [hru, hu]
    ihave #HreqK : kbReq (GF := GF) (some d') X Y $$ []
    · simp only [kbReq]
      iunfold bkReq
      iright
      iexists (lateW d'.gx), Pk'
      iframe Hbk'
      iunfold storageReq at Hreq
      iexact Hreq
    by_cases hf : f = func.nil
    · -- the hook unset (at any share): the caller's view shift
      subst hf
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
    · -- the hook set, frozen: the caller's triple
      have hdq : dq = DFrac.discard := by
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
  -- the client's update, as the takeover's ghost step
  iunfold mvccState at HAU
  ihave Hcb := restoreCb_of_au γ p σ' Hσ'.2 Hσ'.1 c hc Q $$ [Hcra HAU]
  · iframe Hcra Hrc2 HAU
  rw [← hrc, hL]
  rw [hL] at Hlok
  -- the plain open token's fields' quarter and deposit
  iunfold openRest at Hor
  simp only [Hwq, Bool.false_eq_true, ↓reduceIte]
  icases Hor with ⟨%hcmo, HfsQ, Hwsd, Htk2⟩
  -- the internal `Restore`, at the store's current names (the first log as its `L`)
  iapply (hRst s ((γ : StoreNames).withPhys p) (storageVal (d' : MvccStorage)) d'
      γ.bucket Pk' [[], []] R c r L iprop(crevAuth γ.api (1 : Qp).half.half r.crev ∗ ∃ σ, Q σ)
      hkH dqh PreH QH PostH XH YH hlok)
    $$ [HbkT HcrT Himg Hrr Hreg Hsr Hrts Hctx HLo HF Hcb Hright Hwo Hcur' HfsQ Hwsd] [-]
  · have hpk' : ((γ : StoreNames).withPhys p).kb = some d := hpk
    ihave #HpF : crevPermAt (GF := GF) ((γ : StoreNames).withPhys p) r.finRev $$ []
    · iapply crevPermAt_of _ (fun _ => iprop(True))
      isplitl
      · iapply (crevPermIs_cperm (γ : StoreNames) ((γ : StoreNames).withPhys p) rfl
          (fun _ => iprop(True)))
        iexact Hperm
      · iintro !>; itrivial
    ihave #HpC : crevPermAt (GF := GF) ((γ : StoreNames).withPhys p) r.crev $$ []
    · iapply crevPermAt_of _ (fun _ => iprop(True))
      isplitl
      · iapply (crevPermIs_cperm (γ : StoreNames) ((γ : StoreNames).withPhys p) rfl
          (fun _ => iprop(True)))
        iexact Hperm
      · iintro !>; itrivial
    rw [isStore_withPhys]
    iframe Hpkg Hrc HpF HpC Hs Himg HndO Hrr Hreg Hsr Hwts' Hrts Hctx Hcb Hwo
    simp only [StoreNames.withPhys_api, StoreNames.withPhys_leases, StoreNames.withPhys_watchQ,
      Hwq, Bool.false_eq_true, ↓reduceIte, StoreNames.withPhys_idx_hist]
    isplitr
    · ipureintro; exact ⟨d, hpk', by rw [hcm', hcm]⟩
    isplitl [Hright]
    · unfold restoreRightM
      simp only [hpk', kbCmpM, hcm, ↓reduceIte]
      iexact Hright
    isplitl [HfsQ]
    · iunfold fieldShare at HfsQ; iunfold fieldShare
      icases HfsQ with ⟨%p0, %o0, Hf⟩
      iexists p0, o0
      simp only [StoreNames.withPhys_withPhys]
      iexact Hf
    isplitl [Hwsd]
    · iunfold wsDep at Hwsd; iunfold wsDep; simp only [StoreNames.withPhys_wsd]; iexact Hwsd
    isplitl [Hcur']
    · iunfold writerFrag; iexists o'; iexact Hcur'
    isplitr
    · rw [idxCert_withPhys]; iexact HcL0
    isplitr
    · itrivial
    isplitr
    · iunfold certOk; iright; iright; iunfold certFree at Hfree
      simp only [StoreNames.withPhys_cok]; iexact Hfree
    isplitl [HbkT]
    · iintro %q %hq; simp only [StoreNames.withPhys_withPhys]; iapply HbkT $$ %q %hq
    isplitl [HcrT]
    · iintro %q %hq; simp only [StoreNames.withPhys_withPhys]; iapply HcrT $$ %q %hq
    isplitl [HLo]
    · iunfold mvccLeases at HLo; iexact HLo
    isplitr
    · ipureintro; exact Hlok
    iexact HF
  -- the post: the open token and the backend share at the new names, the old storage's shares
  inext
  simp only [StoreNames.withPhys_withPhys, StoreNames.withPhys_api, StoreNames.withPhys_leases]
  iintro ⟨%p'', %hp'', Hcl, HfsQ, Hwsd, Hfrag, Hwo', #Hhp', #Hreg', -, -, HrB, Hjob, Hold, Hnew,
    HLo, HF, -, ⟨Hcra', %σ0, HQ⟩, -⟩
  icases Hback $$ HrB with ⟨Hhook, Hres⟩
  have hkp'' : ((γ : StoreNames).withPhys p'').kb = some d' := hp''.2
  have hcmp'' : kbCmpM ((γ : StoreNames).withPhys p'').kb := by rw [hkp'']; exact hcm'
  have hj : nJobRd ((γ : StoreNames).withPhys p).kb = 1 := by
    show nJobRd ((γ : StoreNames).withPhys p).kb = 1
    rw [show ((γ : StoreNames).withPhys p).kb = some d from hpk]; simp [nJobRd, hcm]
  iapply HΦ
  iframe Htt Hres Hhook
  isplitl [Hcl Hcra' Hnew HfsQ Hwsd Hwo' Htk2]
  · iunfold mvccOpen
    iexists s, p'', r.crev
    iframe Hloc
    isplitl [Hcl]
    · iapply (storeCloserM_on _ _ _ hcmp'').1; iexact Hcl
    iframe Hcra' Hnew
    isplitr
    · rw [show p''.kb = some d' from hp''.2]; iexact Hwts'
    isplitr
    · ipureintro; exact CmpRecs.crev_ge _ r hrec
    isplitl [HfsQ Hwsd Htk2]
    · iunfold openRest
      simp only [Hwq, Bool.false_eq_true, ↓reduceIte]
      isplitr
      · ipureintro; show kbCmpM p''.kb; rw [show p''.kb = some d' from hp''.2]; exact hcm'
      isplitl [HfsQ]
      · iunfold fieldShare at HfsQ; iunfold fieldShare
        icases HfsQ with ⟨%p0, %o0, Hf⟩
        iexists p0, o0
        simp only [StoreNames.withPhys_withPhys] at *
        iexact Hf
      isplitl [Hwsd]
      · iunfold wsDep at Hwsd; iunfold wsDep; simp only [StoreNames.withPhys_wsd] at *; iexact Hwsd
      iexact Htk2
    iexact Hwo'
  isplitl [HF Hfrag]
  · iunfold mvccBackend
    iframe HF
    iunfold writerFrag at Hfrag
    icases Hfrag with ⟨%o2, Hcur2⟩
    iexists p'', o2, d'
    iframe Hcur2 Hbk'
    isplitr
    · ipureintro; exact ⟨hp''.2, hcm', rfl⟩
    isplitr
    · iintro !>; iexists s; iexact Hreg'
    isplitr
    · iexact Hhp'
    isplitr
    · iintro !> Hlc
      unfold storeWT kbWT
      rw [hkp'']
      iapply Hsup' $$ Hlc
    ipureintro; exact hlp'
  isplitl [Hold Hjob HRT]
  · iunfold storageRest
    rw [hj]
    unfold compactJobResM
    simp only [show kbCmpM ((γ : StoreNames).withPhys p).kb from by
      rw [show ((γ : StoreNames).withPhys p).kb = some d from hpk]; exact hcm, ↓reduceIte]
    icases Hjob with ⟨Hjrt, -⟩
    have h3 : 3 ≤ nReaders := by rw [nReaders_val]; omega
    have hn : nReaders = (nReaders - 1 - 1) + 1 + 1 := by omega
    have hrt : storeRT (GF := GF) ((γ : StoreNames).withPhys p) = kbRT (some d) := by
      unfold storeRT; rw [show ((γ : StoreNames).withPhys p).kb = some d from hpk]
    rw [hrt]
    rw [show ((γ : StoreNames).withPhys p).kb = some d from hpk] at *
    rw [hn, List.replicate_succ, List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    isplitl [HRT]
    · unfold kbRT; icases HRT with ⟨-, H⟩; iexact H
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hjrt]
    · unfold kbRT; icases Hjrt with ⟨-, H⟩; iexact H
    rw [show nReaders - 1 - 1 + 1 + 1 - 1 - 1 = nReaders - 1 - 1 by omega]
    iapply rep_kbRT_bOpen
    iexact Hold
  iunfold mvccLeases
  iframe HLo
  iexists σ0; iexact HQ

end proof

end api
end mvcc
end EtcdGrove
end Perennial
