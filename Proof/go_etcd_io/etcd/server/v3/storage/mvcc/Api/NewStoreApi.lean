/-
**`NewStore.spec` over mvcc's storage abstraction** (M3, 2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

* `imageOk_start`: the image of the empty history has an empty `Key` bucket and no compaction
  record (`noCmpData`).
* `NewStore.wp_proof`: `NewStore.spec` (the API's) from the internal `mvcc.NewStore.spec` and the
  bridge's backend specs: `mvccStorageFor` at `mvccStart` gives the internal premises (the bridge's
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

/-- **`NewStore.spec`** (the API's) from the internal one and the bridge's backend specs. -/
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
  intro lg le cfg B Pk γl rd0 hcfg hrb hth
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, Hfor, Hlrd, #Hle, Hro⟩ HΦ
  iunfold mvccStorageFor at Hfor
  icases Hfor with ⟨%bk, %D, %Hf, #Hrc, #Hb, #Hsz, Hv, Hdl, Hfk, Hsr, Hrs, Hrg, Hw1, Hw2, #Hsup,
    Hopen⟩
  obtain ⟨hB, hP, hcm, himg, hlp⟩ := Hf
  subst hB
  obtain ⟨hk0, hnc⟩ := imageOk_start himg
  -- the internal premises: the bridge's contract at fresh index names, the view, the token
  imod idxFresh_alloc (GF := GF) with ⟨%γi, Hifresh⟩
  imod storeDlReg_fix bk.γB γi $$ Hdl with #Hreg
  icases bkNoCmp_fkV_of_fkCl bk.γB bk.P hnc $$ Hfk with ⟨Hncmp, #Hfv⟩
  ihave #Hsz1 := Hsz $$ %bk.γB %bk.be
  ihave #Hbk := storeBackend_of_backendC hCRT hRT hBT hFC hSz hSzU hcRL hcRU hcUR hrRL hrRU hrUR
    hLI hLO hSP hUL hbUR hCB hDel hID hName hSafe hLSR hUSR hUP bk hP Pk γl γi
    $$ [$Hbpkg $Hsch $Hb $Hsz1 $Hreg $Hfv]
  imod ghost_map_alloc_empty (K := w64) (V := Log) (GF := GF) with ⟨%γok, Hok0⟩
  ihave Hrts := bkRTx_of_rdToks bk.γB bk.P bk.be nReaders $$ [Hrs Hopen]
  · iframe Hrs Hopen
  haveI : ReceiptBoundLe GF (2 ^ 48) := ⟨hrb⟩
  have hsv : storageVal (bk : MvccStorage) =
      interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #bk.be := rfl
  rw [hsv]
  iapply wp_fupd
  wp_apply +noauto (hNewStore lg _ le cfg (some bk) γl γl Pk #func.nil rd0 false γi γok
      (fun _ => iprop(True)) hcfg)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hsr Hrts Hlrd Hro Hifresh Hok0]
    as %s ⟨%γ, %Hγ, #Hs, ⟨%rd, Hro, #Hrc⟩, Hcok, #Hhk, ⟨%rv, %wv, HrvF, #HrvI, HwvF, #HwvI⟩, Hrds, -, -, Hcl, -, -, Hfrag, Hcu, Hret,
      #Hcp, #Hwreg, ⟨%pr, %hpr, Hnc⟩, Hlc1⟩
  · iframe Hle Hro Hifresh Hok0
    isplitr
    · iexact Hbk
    rw [show kbRT (GF := GF) (some bk) = bkRTx bk.γB bk.P bk.be from rfl]
    simp only [kbView_some, kbNoCmp_some, kbRegRight_some, kbNoDelOff, kbCmpM, hcm, kbWT,
      kbSRM, kbSR, ↓reduceIte]
    isplitl [Hv]
    · unfold bkView
      iexists _
      isplitl [Hv]
      · unfold backend.bView; iexists true; iexact Hv
      ipureintro
      exact keyView_of_dget hP (fun k => by rw [hk0]; rfl)
    iframe Hncmp Hrg Hw1 Hw2 Hsr Hrts Hlrd
  obtain ⟨-, hγl, hγk, hγw, -, -, -⟩ := Hγ
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
  icases Hnc with ⟨Hab, Hpn, Hcr2, Hcr4, #Hlb, Htok, Hnl, #Hloc⟩
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
  -- (2026-11-06) and one for the writer's own (`writerOwn`, which `Restore` takes)
  imod storeReader_retire2 s γ _ o (nJobRd (some bk)) $$ Hlc1 Hs Hcur Hrd1 Hrd2 Hret
    with ⟨HRT, HRTw, Hret, Hcur⟩
  -- the readers' supply from the rest (track A, request 3): every thread but one
  have hpool : threadBound GF ≤ (nReaders - nJobRd (some bk) - 2) + 1 := by
    have h1 : mvccReaderN = backend.rdStockN - 6 := rfl
    have h2 : nReaders = backend.rdStockN - 2 := rfl
    have : 6 ≤ backend.rdStockN := by rw [backend.rdStockN_val]; omega
    have : nJobRd (some bk) ≤ 1 := nJobRd_le (some bk)
    omega
  imod rdSupply_init ((nroot .@ "mvcc") .@ "storeRdPool") s γ _ hpool $$ Hrds with #Hsupp
  -- the certificate map's free entry
  imod ghost_map_insert_persist (W64 0) ([] : Log) (GMap.lookup_empty _) $$ Hcok with ⟨-, #Hfree⟩
  ihave #Hfree' : certFree (GF := GF) γ $$ []
  · iunfold certFree; iexact Hfree
  ihave #Hwts : □ (⧗ 1 ={⊤}=∗ storeWT (GF := GF) γ) $$ []
  · unfold storeWT kbWT; rw [show γ.kb = some bk from hγk]; iexact Hsup
  -- the compaction right from the closer
  imod compactRightR_of_closer s γ ⊤ $$ Hcl Hcu with Hright
  -- the initial log's receipt (`mvccState`'s: nothing changed yet)
  imod (preceipt_zero (GF := GF)) with #Hr0
  ihave #Hr0' : ⧖ (logCh ([[], []] : Log)) $$ []
  · rw [show logCh ([[], []] : Log) = 0 from rfl]; iexact Hr0
  -- the handle
  ihave #Hmv : □ isMvcc (GF := GF) (interface.mkOk (go.GoType.PointerType store.ty) #s) γ $$ []
  · iintro !>
    iunfold isMvcc
    iintro !>
    ileft
    isplitl
    · iunfold isMvccPlain
      iexists s
      iframe Hs Hloc Hcp Hsupp Hfree'
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
    rw [show (mvccStart : MvccState) = ⟨[[], []], -1, none⟩ from rfl]
    simp only [MvccState.notifiedLog]
    iframe Hab Hpn Hcr2 Hnl
    iframe Hr0'; ipureintro; exact MvccReachable.start
  isplitl [Hright Hcr4 HRT HRTw Hret]
  · iunfold mvccOpen
    iexists s, γ.phys, (-1)
    rw [StoreNames.withPhys_self]
    iframe Hloc Hright Hcr4 HRT
    isplitr
    · rw [show γ.phys.kb = some bk from hγk]
      simp only [kbWTSupplyM, kbCmpM, hcm, kbWTSupply, ↓reduceIte]
      iexact Hsup
    isplitr
    · ipureintro; exact Int.le_refl _
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
    itrivial
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
    iunfold hookInit at Hhk
    icases Hhk with ⟨#HhP, -⟩
    isplitr
    · iintro !>; iexact HhP
    isplitr
    · iexact Hwts
    ipureintro; exact hlp
  iexists rd
  iframe Hro
  iapply (mvccDeleter_of hTODO _ _ (store.Write.wp_api hWr s) rd γ) $$ [$Hpkg $Hmv $Hrc]

end proof

end api
end mvcc
end EtcdGrove
end Perennial
