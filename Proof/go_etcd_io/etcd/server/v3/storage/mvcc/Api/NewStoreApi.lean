/-
**`NewStore.spec` over mvcc's storage abstraction** (M3, 2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

* `imageOk_start`: the image of the empty history has an empty `Key` bucket and no compaction
  record (`noCmpData`).
* `NewStore.wp_proof`: `NewStore.spec` (the API's) from the internal `mvcc.NewStore.spec` and the
  bridge's backend specs (B3, 2026-11-10: at any image, `ImageBridge.lean`; until then as follows):
  `mvccStorageFor` at `mvccStart` gives the internal premises (the bridge's
  contract `storeBackend_of_backendC` over the registration fixed at fresh index names, the empty
  view, the exact no-compaction token and the bit from the open's `fkCl`, the reader tokens, the
  safe-range slot); the post's `isMvcc` (`isMvccPlain`: the store, its location, the permit `True`),
  `mvccState γ mvccStart` (the client's parts `api.newClient`), `mvccOpen` (the compaction right
  from the closer, its quarter of the authority, a reader retired from the pool, the supply) and the
  whole backend share (`mvccBackend γ 1`).
* The range deleter's contract (`mvccDeleter`): `NewStore`'s `rdCalls` (the closure is the store's
  `Write` at a fresh trace) and `KV.Write.contract` at `*store` (`mvccDeleter_of`, 2026-11-06; until
  then the placeholder `mvccDeleter_M1`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Retire2
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RdSupply
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.DeleterApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WriteApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.ImageBridge
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- **The image of the empty history**: an empty `Key` bucket and no compaction record. -/
theorem imageOk_start {D : backend.Data} (h : snap.imageOk D mvccStart.log mvccStart.crev false) :
    (∀ k, backend.dget D keyName k = none) ∧ noCmpData D := by
  obtain ⟨rc, ents, hk, hfin, hsch, -, hpos, hcut, hrc, hu, -⟩ := h
  have he : ents = [] := by
    have hs := hcut.1
    rw [show logEnts mvccStart.log 0 mvccStart.log.length = [] from by decide] at hs
    exact List.sublist_nil.1 hs
  subst he
  have hfr : rc.finRev = -1 := by
    have h1 : mvccStart.crev = -1 := rfl
    unfold CmpRecs.crev at hrc; rw [hu, h1] at hrc; simpa using hrc
  have hf : rc.fin = none := by
    cases hx : rc.fin with
    | none => rfl
    | some x =>
      have := hpos.1 x hx
      unfold CmpRecs.finRev at hfr; rw [hx] at hfr; simp at hfr; omega
  have hs : rc.sched = none := by
    cases hx : rc.sched with
    | none => rfl
    | some x =>
      have h1 := hpos.2 x hx
      have h2 : rc.resumes = true := by
        unfold CmpRecs.resumes CmpRecs.schedRev; rw [hfr, hx]; simp; omega
      rw [h2] at hu; cases hu
  refine ⟨fun k => by rw [hk]; rfl, ?_, ?_⟩
  · rw [hsch, hs]; rfl
  · rw [hfin, hf]; rfl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- Each reader slot's token with the reader's share of the open token (`bkRTx`). -/
theorem bkRTx_of_rdToks (γ : backend.BNames) (P : backend.BParams) (b : Loc) : ∀ n : Nat,
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
    iapply bkRTx_of_rdToks γ P b n
    iframe Hr Ho

/-- **`NewStore.spec`** (the API's) from the internal one and the bridge's backend specs (B3,
mvccfull's Freeze, 2026-11-10; until then of the fresh statement, commit `ae30739dde`): the storage
at its image as the internal `NewStore` takes it (`newStore_of_storage`, `ImageBridge.lean`), the
resumed compaction's context (`resumeCtx_of_api`), the certificate map's free entry before the call;
after it, the restorable compaction right at the restored revision (`storeCloserM_on`), the client's
state at `σ` from `newClient`, the initial log's certificate from `isStore`. -/
theorem NewStore.wp_proof
    (hNewStore : mvcc.NewStore.spec (GF := GF) (hG := hG))
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
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hWr : mvcc.store.Write.spec (GF := GF) (hG := hG)) :
    NewStore.spec (GF := GF) (hG := hG) := by
  intro hrbI lg le cfg B Pk γl rd0 σ u Ls dq f Pre Q' Post X Y
  have hrb : receiptBound GF ≤ 2 ^ 48 := hrbI.receiptBound_le
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hzl, Hfor, %Hpre, Hlrd, #Hle, Hro, HLo, %HLs, Hif⟩ HΦ
  obtain ⟨hcfg, hreach, hpend⟩ := Hpre
  -- the index's names; the storage at its image
  imod idxFresh_alloc (GF := GF) with ⟨%γi, Hifresh⟩
  icases newStore_of_storage hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR hLI hLO hSP hUL
      hbUR hCB hDel hID hName hSafe hLSR hUSR hUP hrb B Pk σ.log σ.crev u γl γi
      $$ [$Hbpkg $Hsch $Hfor]
    with ⟨%bk, %r, %R, %Hb, Hrcpt, #Hrc, #Hsess, HbkT, HcrT, Himg, HndO, Hrg, Hreg, Hw1, Hw2,
      Hsr, #Hsup, Hrts, #Hb, #Hwbs⟩
  obtain ⟨hB, hcm, hL, hlok, hrc, hru, hlp, hrec⟩ := Hb
  subst hB
  rcases σ with ⟨log, crev, pend⟩
  simp only at hL hrc hpend hreach HLs ⊢
  subst hL hrc hpend
  -- the resumed compaction's context
  icases resumeCtx_of_api bk r u hru Pk dq f Pre Q' Post X Y $$ [$Hb $Hif]
    with ⟨%hkH, %dqh, %PreH, %QH, %PostH, %XH, %YH, Hctx, Hback⟩
  -- the certificate map, with its free entry
  imod ghost_map_alloc_empty (K := w64) (V := Log) (GF := GF) with ⟨%γok, Hok0⟩
  imod ghost_map_insert_persist (W64 0) ([] : Log) (GMap.lookup_empty _) $$ Hok0 with ⟨Hok0, #Hfree⟩
  iapply wp_fupd
  wp_apply +noauto (hNewStore lg _ le cfg bk γl γl Pk rd0 false γi γok _ (fun _ => iprop(True))
      R r Ls hkH PreH QH PostH XH YH dqh)
    $$ [HbkT HcrT Himg Hrcpt HndO Hrg Hreg Hw1 Hw2 Hsr Hrts Hlrd Hro HLo Hifresh Hok0 Hctx]
    as %s ⟨%γ, %Hγ, #Hs, ⟨%rd, Hro, #Hrdc⟩, Hcok, #Hhk, ⟨%rv, %wv, HrvF, #HrvI, HwvF, #HwvI⟩,
      Hrds, #HcL, -, Hcl, -, HfsQ, Hwsd, Hfrag, Hret, #Hcp, #Hwreg, ⟨%pr, %hpr, Hnc⟩, HLo, HrB,
      Hlc1⟩
  · iframe Hpkg Hzl Hle Hro Hifresh Hok0 Hsess HbkT HcrT Himg Hrcpt HndO Hrg Hreg Hw1 Hw2 Hsr Hrts
      Hlrd HLo Hctx
    isplitr
    · ipureintro; exact ⟨hcfg, hlok⟩
    isplitr
    · ipureintro; exact HLs
    isplitr
    · iright; iright; iexact Hfree
    isplitr
    · iright; iintro !>; itrivial
    isplitr
    · iright; iintro !>; itrivial
    cases r.resumes
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [↓reduceIte]; iexact Hsup
  obtain ⟨-, hγl, hγk, hγw, -, hγc, -⟩ := Hγ
  icases Hback $$ HrB with Hres
  -- the initial log's certificate (the store's)
  ihave #Hs' := Hs
  iunfold isStore at Hs'
  icases Hs' with ⟨%le', %lg', %scfg, %shs, Hs'⟩
  iNamed Hs'
  -- the views, for good (a store without watchers: no watchable store rewrites them)
  ipersist HrvF
  ipersist HwvF
  -- the pending revision's client part: half (a plain store)
  have hpr' : pr = (1 : Qp).half := by
    unfold pndW at hpr
    rw [hγw] at hpr
    simp only [Bool.false_eq_true, ↓reduceIte] at hpr
    rw [Qp.ext_iff] at hpr ⊢
    simp only [Qp.val_add, Qp.val_half, Qp.val_one] at hpr ⊢
    grind
  subst hpr'
  iunfold api.newClient at Hnc
  icases Hnc with ⟨Hab, Hpn, Hcr2, Hcr4, #Hlb, Htok, Hnl, #Hloc, Hrdk⟩
  -- a reader retired from the pool for the open token's reader (the compactor's)
  iunfold writerFrag at Hfrag
  icases Hfrag with ⟨%o, Hcur⟩
  have hn : nReaders - nJobRd (some bk) = (nReaders - nJobRd (some bk) - 2) + 1 + 1 := by
    have : 3 ≤ nReaders := by rw [nReaders_val]; omega
    have : nJobRd (some bk) ≤ 1 := nJobRd_le (some bk)
    omega
  rw [hn, List.replicate_succ, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hrd1, Hrds⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hrd2, Hrds⟩
  ihave Hrd1 : storeReader (GF := GF) s γ $$ [Hrd1]
  · iunfold storeReader; iexact Hrd1
  ihave Hrd2 : storeReader (GF := GF) s γ $$ [Hrd2]
  · iunfold storeReader; iexact Hrd2
  -- and one for the writer's own (`writerOwn`, which `Restore` takes)
  imod storeReader_retire2 s γ _ o (nJobRd (some bk)) $$ Hlc1 Hs Hcur Hrd1 Hrd2 Hret
    with ⟨HRT, HRTw, Hret, Hcur⟩
  -- the rest: two readers' tickets the open token's, the other readers in the reader tokens' pool
  have hN : nReaders - nJobRd (some bk) - 2 = 2 + mvccReaderN := by
    have h1 : mvccReaderN = backend.rdStockN - 7 := rfl
    have h2 : nReaders = backend.rdStockN - 2 := rfl
    have : 7 ≤ backend.rdStockN := by rw [backend.rdStockN_val]; omega
    have : nJobRd (some bk) = 1 := by simp [nJobRd, hcm]
    omega
  rw [hN]
  rw [show List.replicate (2 + mvccReaderN) () = List.replicate 2 () ++ List.replicate mvccReaderN ()
    from List.replicate_append_replicate.symm]
  icases BigSepL.bigSepL_append.1 $$ Hrds with ⟨Hrd2s, Hrds⟩
  imod storeReaders_split s γ 2 $$ Hrd2s with ⟨-, Htk2⟩
  imod rdSupply_init s γ _ $$ [Hrdk Hrds] with ⟨#Hsupp, Htks⟩
  · iframe Hrdk Hrds
  -- the certificate map's free entry
  ihave #Hfree' : certFree (GF := GF) γ $$ []
  · iunfold certFree; rw [hγc]
    iexact Hfree
  ihave #Hwts : □ (⧗ 1 ={⊤}=∗ storeWT (GF := GF) γ) $$ []
  · unfold storeWT kbWT; rw [show γ.kb = some bk from hγk]; iexact Hwbs
  -- the compaction right, from the closer at the restored revision
  have hcmγ : kbCmpM γ.kb := by rw [hγk]; exact hcm
  icases (storeCloserM_on s γ r.crev hcmγ).1 $$ Hcl with Hright
  -- the handle
  ihave #Hmv : □ isMvcc (GF := GF) (interface.mkOk (go.GoType.PointerType store.ty) #s) γ $$ []
  · iintro !>
    iunfold isMvcc
    iintro !>
    ileft
    isplitl
    · iunfold isMvccPlain
      iexists s
      iframe Hs Hloc Hcp Hsupp Hfree' Hc0
      isplitr
      · ipureintro; rfl
      iexists rv, wv
      iframe HrvF HrvI HwvF HwvI
    ipureintro; exact hγw
  imodintro
  iapply HΦ
  iexists γ
  isplitr
  · ipureintro; exact hγl
  isplitr
  · iexact Hmv
  isplitl [Hab Hpn Hcr2 Hnl]
  · iunfold mvccState
    iunfold api.mvccStateI
    simp only [MvccState.notifiedLog]
    iframe Hab Hpn Hcr2 Hnl Hrc
    ipureintro; exact hreach
  isplitl [Hright Hcr4 HRT HRTw Hret HfsQ Hwsd Htk2]
  · iunfold mvccOpen
    iexists s, γ.phys, r.crev
    rw [StoreNames.withPhys_self]
    iframe Hloc Hright Hcr4 HRT
    isplitr
    · rw [show γ.phys.kb = some bk from hγk]
      simp only [kbWTSupplyM, kbCmpM, hcm, kbWTSupply, ↓reduceIte]
      iexact Hwbs
    isplitr
    · ipureintro; exact CmpRecs.crev_ge _ r hrec
    ihave Hwo : writerOwn (GF := GF) γ $$ [HRTw Hret]
    · iunfold writerOwn
      iframe HRTw
      have hwo : 2 + nJobRd γ.kb = nJobRd (some bk) + 2 := by
        rw [show γ.kb = some bk from hγk]; omega
      rw [hwo]; iexact Hret
    iframe Hwo
    iunfold openRest
    rw [hγw]
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr
    · ipureintro; show kbCmpM γ.phys.kb; rw [show γ.phys.kb = some bk from hγk]; exact hcm
    iframe HfsQ Hwsd Htk2
  isplitl [Htok Hcur]
  · iunfold mvccBackend
    iframe Htok
    iexists γ.phys, o, bk
    rw [StoreNames.withPhys_self]
    iframe Hcur Hb
    isplitr
    · ipureintro; exact ⟨hγk, hcm, rfl⟩
    isplitr
    · iintro !>; iexists s; iexact Hwreg
    isplitr
    · iintro !>; iexact Hhk
    isplitr
    · iexact Hwts
    ipureintro; exact hlp
  isplitl [Htks]
  · iunfold mvccReaders; iexact Htks
  iframe HLo Hrc Hres
  iexists rd
  iframe Hro
  iapply (mvccDeleter_of hTODO _ _ (store.Write.wp_api hWr s) rd γ) $$ [$Hpkg $Hmv $Hrdc]
end proof

end api
end mvcc
end EtcdGrove
end Perennial
