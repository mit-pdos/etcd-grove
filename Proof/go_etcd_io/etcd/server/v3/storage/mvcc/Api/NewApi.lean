/-
**`New.spec` over mvcc's storage abstraction** (track A, 2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

* `New.wp_proof`: `New.spec` (the API's) from the internal `mvcc.New.spec` and the bridge's backend
  specs, as `NewStore.wp_proof`: `mvccStorageFor` at `mvccStart` gives the internal premises; the
  post's `isMvcc` (`isMvccWatchable`: the watchable store, the watch tokens' pool from its tokens, the
  readers' pool from its reader slots but the compactor's, the inner store's location, the permit
  `True`), `mvccState γ mvccStart` (the client's parts the internal `New` returns, the lock's quarter
  of the pending revision gone into its slot), `mvccOpen` (the compaction right from the inner
  closer, its quarter of the authority, a reader retired, the supply, and the watchable store's own
  closer, `openRest`) and the whole backend share (`mvccBackend γ 1`). The range deleter from
  `New`'s `rdCalls` and `KV.Write.contract` at `*watchableStore` (`mvccDeleter_of`, 2026-11-06).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Retire2
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.NewStoreApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RdSupply
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WatchTxnApi
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

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **`New.spec`** (the API's) from the internal one and the bridge's backend specs (B3, mvccfull's
Freeze, 2026-11-10; the proof of the fresh statement is at commit `ae30739dde`). Steps 1-4 and 7 are
`newStore_of_storage` (`ImageBridge.lean`), step 6 `resumeCtx_of_api`. Outline (the bridge `Restore`'s API proof uses),
in the order of `NewApi.lean`'s `New.wp_proof`, with `RestoreApi.lean`'s bridge in place of
`imageOk_start`:

1. `mvccStorageFor B Pk σ.log σ.crev u` opened as `restore_of_storage` does: `bk`, `D`, the image
   `imageOk D σ.log σ.crev u` (`snap.imageOk_keyImageM`: records `r` with `r.crev = σ.crev`,
   `r.resumes = u`, `keyImageM true σ.log r D`), `σ.log = [[], []] ++ R` with `restoreLogOk R`
   (`restoreLog_ch`, the `IdxWf` from `LogB`/`LogWf'`), `recsSign r`, the receipt `⧖ (logCh σ.log)`
   (→ `restoreRcptM bk σ.log`, mode on). `restore_of_storage` is `private` and quantifies over
   `γ.withPhys p` for a given `γ`; its body is what is reused, at `∀ γ` with `γ.idx = γi`.
2. The index's names `γi` (`idxFresh_alloc`). The registration stays unfixed (`dlInit`, which is
   `restoreRegM bk` on). The session contract comes from `storeSessT_of_backendC`
   (`NewStoreSessReal.lean`: `isKeyBackendG_of_backendC` at `bkDel`, no registration). The contract
   at the records behind the fix comes from `storeBackendTR_of_backendC … γi r hsign` under
   `restoreFixM bk γ = storeDlReg bk.γB γ.idx` (on, `γ.idx = γi`). It needs `fkV … true`, from
   `fkV_of_fkCl` with `fkWfD_of_keyImageM`.
3. The image `restoreImageM bk γb σ.log r` from `restoreImageM_of_openOn` (`bView` and `fkCl`).
4. The clean read is `keyCleanRead_of_backendC`, lent `storeRT γ ∗ dlInit bk.γB`, which is
   `restoreRegM bk` on. `NewStore` fixes the registration itself once `restore()` gives the token
   back (`storeSess_fix`). (Until 2026-11-09 this step needed R1's bridge lemma over a registration
   fixed at step 2. The Probe found that `NewStore`'s batch session needs no registration:
   `NewStoreSess.lean`.)
5. The certificate map: `ghost_map_alloc_empty`, then `ghost_map_insert_persist 0 []` before the
   call (`M = {0 ↦ []}`, the third disjunct; the API's `certFree` is that element).
6. The permit: `Perm := fun _ => True` (both disjuncts' right side); the lessor: `leaseOwn γl Ls ∅`
   and the items' premise are the API's verbatim; the resumed compaction: the API's `if u then …` to
   `resumeCtxM bk r Pk (some #f | none) …` exactly as `watchableStore.Restore.wp_api` builds it
   from `storageHook`/`hookRun`/`storageReq` (with `kbWTSupplyM` from `mvccStorageFor`'s supply).
7. The readers, the safe-range slot, `kbRegRight`, the two write tokens, `kbNoDelOff` (`True` on):
   from `mvccStorageFor`, as today.
8. After the call: `wsCloserM_on` gives `wsCloserR … σ.crev`, which is `openRest`'s and
   `mvccOpen`'s right at `σ.crev` (today made from `compactRightR_of_closer` at `-1`); `newClient
   … σ.log σ.crev` gives `mvccState γ σ` (`MvccReachable σ`, `σ.pending = none` from the premises;
   `idxCert`'s receipt for `mvccStateI`'s `⧖`); `storeReader_retire2`, `rdkPool_init`,
   `watchTokPool_alloc` as today; `resumeBackM` to the API's `if u then storageHook … ∗ Post ∗ Y`
   (`resumeBackM_of`'s inverse reading, as `Restore`'s API proof); `mvccBackend γ 1 B Pk` as today,
   with `hookP`; the receipt `⧖ (logCh σ.log)` from step 1's (persistent). -/
theorem New.wp_proof
    (hNew : mvcc.New.spec (GF := GF) (hG := hG))
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
    New.spec (GF := GF) (hG := hG) := by
  intro hrbI lg le cfg B Pk γl rd0 σ u Ls dq f Pre Q' Post X Y
  have hrb : receiptBound GF ≤ 2 ^ 48 := hrbI.receiptBound_le
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, #Hzl, Hfor, %Hpre, Hlrd, #Hle, Hro, HLo, %HLs, Hif⟩ HΦ
  obtain ⟨hcfg, hreach, hpend⟩ := Hpre
  -- 1-2. the index's names; the storage at its image (`newStore_of_storage`)
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
  -- 6. the resumed compaction's context
  icases resumeCtx_of_api bk r u hru Pk dq f Pre Q' Post X Y $$ [$Hb $Hif]
    with ⟨%hkH, %dqh, %PreH, %QH, %PostH, %XH, %YH, Hctx, Hback⟩
  -- 5. the certificate map, with its free entry
  imod ghost_map_alloc_empty (K := w64) (V := Log) (GF := GF) with ⟨%γok, Hok0⟩
  imod ghost_map_insert_persist (W64 0) ([] : Log) (GMap.lookup_empty _) $$ Hok0 with ⟨Hok0, #Hfree⟩
  iapply wp_fupd
  wp_apply +noauto (hNew lg _ le cfg bk γl γl Pk rd0 γi γok γl _ (fun _ => iprop(True))
      R r Ls hkH PreH QH PostH XH YH dqh)
    $$ [HbkT HcrT Himg Hrcpt HndO Hrg Hreg Hw1 Hw2 Hsr Hrts Hlrd Hro HLo Hifresh Hok0 Hctx]
    as %ws ⟨%st, %γw, %Hγ, #Hws, ⟨%rd, Hro, -, #Hrdc⟩, #Hhk, Htw, Hcok, Hrds, Hcl, Hfrag, Hret,
      #Hcp, #Hwreg, Hnc, HLo, HrB, Hlc1⟩
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
  -- 8. after the call
  obtain ⟨-, hγl, hγk, -, hγc, -, hγcm⟩ := Hγ
  icases Hback $$ HrB with Hres
  have hcm' : γw.st.cm = true := by rw [hγcm]; exact hcm
  have hjr : nJobRd (some bk) = 1 := by simp [nJobRd, hcm]
  ihave #Hws' := Hws
  iunfold isWatchableStore at Hws'
  icases Hws' with ⟨%vc, %stc0, %rv, %γv, Hws'⟩
  iNamed Hws'
  iunfold api.newClient at Hnc
  icases Hnc with ⟨Hab, Hpn, Hcr2, Hcr4, #Hlb, Htok, Hnl, #Hloc, Hrdk⟩
  -- a reader retired from the slots for the open token's reader (the compactor's), the rest the
  -- readers' pool
  iunfold writerFrag at Hfrag
  icases Hfrag with ⟨%o, Hcur⟩
  rw [hjr]
  have hn : nReaders - 1 - 2 = (nReaders - 5) + 1 + 1 := by
    have : 5 ≤ nReaders := by rw [nReaders_val]; omega
    omega
  rw [hn, List.replicate_succ, List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hrd1, Hrds⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hrd2, Hrds⟩
  iunfold watchReader at Hrd1 Hrd2
  icases Hrd1 with ⟨Hrd1, -⟩
  icases Hrd2 with ⟨Hrd2, -⟩
  -- and one for the writer's own (`writerOwn`, which `Restore` takes)
  imod storeReader_retire2 st γw.st _ o 1 $$ Hlc1 Hs Hcur Hrd1 Hrd2 Hret with ⟨HRT, HRTw, Hret, Hcur⟩
  -- the readers, their locks' slots and tickets, in the pool of the client's reader tokens
  imod watchReaders_split ws st γw _ $$ Hrds with ⟨Hrds, Htks⟩
  imod rdkPool_init γw.st (watchSlots ws st γw) _ $$ [Hrdk Htks Hrds] with ⟨#Hpool, Htks⟩
  · iframe Hrdk Htks Hrds
  have hrb' : receiptBound GF ≤ 2 ^ 63 - 2 := by omega
  imod watchTokPool_alloc γw ⊤ hrb' $$ Htw with #Htp
  -- the certificate map's free entry
  ihave #Hfree' : certFree (GF := GF) γw.st $$ []
  · iunfold certFree; rw [hγc]; iexact Hfree
  ihave #Hwts : □ (⧗ 1 ={⊤}=∗ storeWT (GF := GF) γw.st) $$ []
  · unfold storeWT kbWT; rw [show γw.st.kb = some bk from hγk]; iexact Hwbs
  -- the inner store's restorable right at the restored revision; the watchable store's own closer
  have hcmγ : kbCmpM γw.st.kb := by rw [hγk]; exact hcm
  icases (wsCloserM_on ws st γw.st r.crev hcmγ).1 $$ Hcl with Hcl
  icases (wsCloserR_iff ws st γw.st r.crev).1 $$ Hcl with ⟨%stc, #Hstc, Hsc, Hwait, Hright⟩
  -- the handle
  ihave #Hmv : □ isMvcc (GF := GF) (interface.mkOk (go.GoType.PointerType watchableStore.ty) #ws)
      γw.st $$ []
  · iintro !>
    iunfold isMvcc
    iintro !>
    iright
    iunfold isMvccWatchable
    iexists ws, st, γw
    iframe Hws Htp Hpool Hloc Hcp Hfree'
    ipureintro; exact ⟨rfl, rfl⟩
  imodintro
  iapply HΦ
  iexists γw.st
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
  isplitl [Hright Hcr4 HRT Hsc Hwait HRTw Hret]
  · iunfold mvccOpen
    iexists st, γw.st.phys, r.crev
    rw [StoreNames.withPhys_self]
    iframe Hloc Hright Hcr4 HRT
    isplitr
    · rw [show γw.st.phys.kb = some bk from hγk]
      simp only [kbWTSupplyM, kbCmpM, hcm, kbWTSupply, ↓reduceIte]
      iexact Hwbs
    isplitr
    · ipureintro; exact CmpRecs.crev_ge _ r hrec
    ihave Hwo : writerOwn (GF := GF) γw.st $$ [HRTw Hret]
    · iunfold writerOwn
      iframe HRTw
      have hwo : 2 + nJobRd γw.st.kb = 1 + 2 := by
        rw [show γw.st.kb = some bk from hγk, hjr]
      rw [hwo]; iexact Hret
    iframe Hwo
    iunfold openRest
    rw [Hwq]
    simp only [↓reduceIte]
    isplitr
    · ipureintro; show kbCmpM γw.st.phys.kb; rw [show γw.st.phys.kb = some bk from hγk]; exact hcm
    iexists ws, rv, stc
    iframe Hrv Hrvkv Hstc Hsc Hwait
  isplitl [Htok Hcur]
  · iunfold mvccBackend
    iframe Htok
    iexists γw.st.phys, o, bk
    rw [StoreNames.withPhys_self]
    iframe Hcur Hb
    isplitr
    · ipureintro; exact ⟨hγk, hcm, rfl⟩
    isplitr
    · iintro !>; iexists st; iexact Hwreg
    isplitr
    · iintro !>; iexact Hhk
    isplitr
    · iexact Hwts
    ipureintro; exact hlp
  isplitl [Htks]
  · iunfold mvccReaders
    have hN : nReaders - 5 = mvccReaderN := by
      have h1 : mvccReaderN = backend.rdStockN - 7 := rfl
      have h2 : nReaders = backend.rdStockN - 2 := rfl
      omega
    rw [← hN]; iexact Htks
  iframe HLo Hrc Hres
  iexists rd
  iframe Hro
  iapply (mvccDeleter_of hTODO _ _ (watchableStore.Write.wp_api hWr ws) rd γw.st) $$ [$Hpkg $Hmv $Hrdc]
end proof

end api
end mvcc
end EtcdGrove
end Perennial
