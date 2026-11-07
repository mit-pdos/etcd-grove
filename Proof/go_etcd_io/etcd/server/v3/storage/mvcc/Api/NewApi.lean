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

/-- **`New.spec`** (the API's) from the internal one and the bridge's backend specs. -/
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
  intro lg le cfg B Pk γl rd0 hcfg hrb
  iintro %Φ ⟨#Hpkg, #Hbpkg, #Hsch, Hfor, Hlrd, #Hle, Hro⟩ HΦ
  iunfold mvccStorageFor at Hfor
  icases Hfor with ⟨%bk, %D, %Hf, #Hrc, #Hb, #Hsz, Hv, Hdl, Hfk, Hsr, Hrs, Hrg, Hw1, Hw2, #Hsup,
    Hopen⟩
  obtain ⟨hB, hP, hcm, himg, hlp⟩ := Hf
  subst hB
  obtain ⟨hk0, hnc⟩ := imageOk_start himg
  -- the internal premises, as `NewStore.wp_proof`'s
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
  wp_apply +noauto (hNew lg _ le cfg (some bk) γl γl Pk #func.nil rd0 γi γok γl
      (fun _ => iprop(True)) hcfg)
    $$ [Hv Hncmp Hrg Hw1 Hw2 Hsr Hrts Hlrd Hro Hifresh Hok0]
    as %ws ⟨%st, %γw, %Hγ, #Hws, ⟨%rd, Hro, -, #Hrc⟩, #Hhk, Htw, Hcok, Hrds, Hcl, Hcr, Hfrag, Hret,
      #Hcp, #Hwreg, Hnc, Hlc1⟩
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
  obtain ⟨-, hγl, hγk, -, -, -, hγcm⟩ := Hγ
  have hcm' : γw.st.cm = true := by rw [hγcm]; simp [kbCmpM, hcm]
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
  -- (2026-11-06) and one for the writer's own (`writerOwn`, which `Restore` takes)
  imod storeReader_retire2 st γw.st _ o 1 $$ Hlc1 Hs Hcur Hrd1 Hrd2 Hret with ⟨HRT, HRTw, Hret, Hcur⟩
  -- (the reader tokens, 2026-11-06; 2026-11-07) the readers, their locks' slots and tickets, in the
  -- pool of the client's reader tokens
  imod watchReaders_split ws st γw _ $$ Hrds with ⟨Hrds, Htks⟩
  imod rdkPool_init γw.st (watchSlots ws st γw) _ $$ [Hrdk Htks Hrds] with ⟨#Hpool, Htks⟩
  · iframe Hrdk Htks Hrds
  have hrb' : receiptBound GF ≤ 2 ^ 63 - 2 := by omega
  imod watchTokPool_alloc γw ⊤ hrb' $$ Htw with #Htp
  -- the certificate map's free entry (track A, request 3)
  imod ghost_map_insert_persist (W64 0) ([] : Log) (GMap.lookup_empty _) $$ Hcok with ⟨-, #Hfree⟩
  ihave #Hfree' : certFree (GF := GF) γw.st $$ []
  · iunfold certFree; iexact Hfree
  ihave #Hwts : □ (⧗ 1 ={⊤}=∗ storeWT (GF := GF) γw.st) $$ []
  · unfold storeWT kbWT; rw [show γw.st.kb = some bk from hγk]; iexact Hsup
  -- the compaction right from the inner closer; the watchable store's own closer kept
  iunfold wsCloser at Hcl
  icases Hcl with ⟨%stc, #Hstc, Hsc, Hwait, Hscl⟩
  rw [show crevRightM (GF := GF) γw.st = crevUB γw.st.idx (1 : Qp).half (-1) from by
    unfold crevRightM; simp [hcm']]
  imod compactRightR_of_closer st γw.st ⊤ $$ Hscl Hcr with Hright
  -- the initial log's receipt (`mvccState`'s: nothing changed yet)
  imod (preceipt_zero (GF := GF)) with #Hr0
  ihave #Hr0' : ⧖ (logCh ([[], []] : Log)) $$ []
  · rw [show logCh ([[], []] : Log) = 0 from rfl]; iexact Hr0
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
    rw [show (mvccStart : MvccState) = ⟨[[], []], -1, none⟩ from rfl]
    simp only [MvccState.notifiedLog]
    iframe Hab Hpn Hcr2 Hnl
    iframe Hr0'; ipureintro; exact MvccReachable.start
  isplitl [Hright Hcr4 HRT Hsc Hwait HRTw Hret]
  · iunfold mvccOpen
    iexists st, γw.st.phys, (-1)
    rw [StoreNames.withPhys_self]
    iframe Hloc Hright Hcr4 HRT
    isplitr
    · rw [show γw.st.phys.kb = some bk from hγk]
      simp only [kbWTSupplyM, kbCmpM, hcm, kbWTSupply, ↓reduceIte]
      iexact Hsup
    isplitr
    · ipureintro; exact Int.le_refl _
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
    iunfold hookInit at Hhk
    icases Hhk with ⟨#HhP, -⟩
    isplitr
    · iintro !>; iexact HhP
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
  iexists rd
  iframe Hro
  iapply (mvccDeleter_of hTODO _ _ (watchableStore.Write.wp_api hWr ws) rd γw.st) $$ [$Hpkg $Hmv $Hrc]

end proof

end api
end mvcc
end EtcdGrove
end Perennial
