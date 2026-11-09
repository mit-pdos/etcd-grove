/-
**DRAFT (B3, mvccfull's F1): the internal `New` on a backend that already holds data**, and the
glue to the API's candidate `api.New.specR` (`ApiNewRestoring.lean`). Candidate restatement of
`mvcc.New.spec` (`New.lean`), over `NewStore.specR`'s premises (`NewStoreR.lean`). Scratch: not
imported, not linked, not proved (`sorry`). Also R1's bridge lemma
(`mvcc.NewStore.cleanRead_of_image`, `sorry`: Probe's target). The internal statement is NOT to
freeze before R1's lemma is proved (`NewStoreR.lean`'s header).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WsCloserR
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.NewApi
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiNewRestoring

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`New(lg, b, le, cfg)` over a real backend `d` holding the image of `L' = [[], []] ++ R` at the
records `r`** (DRAFT, B3). The pre is `newWatchableStore.specR`'s; the post `mvcc.New.spec`'s with
the right to close by the mode at the restored revision (`wsCloser s st γ.st ∗ crevRightM γ.st` →
`wsCloserM s st γ.st r.crev`: on, `wsCloserR`, the inner store's restorable compaction right, with
the resumed job if any; off, `wsCloser`), the API's client parts at `L'` and `r.crev`, the map at
`M`, `hookP` (no `f`), and `newWatchableStore`'s additions (the lessor's owner part at
`pendItems L' []`, `RC`, `resumeBackM`). The loops (`syncWatchersLoop`, `syncVictimsLoop`) start as
today: with no watcher they do nothing of the log. -/
abbrev mvcc.New.specR : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (b le : GoInterface) (cfg : StoreConfig)
    (d : mvcc.KBReal) (γb γl : GName) (P : IProp GF) (rd0 : GoFunc)
    (γi : mvcc.IdxNames) (γok γtag : GName) (M : GMap w64 mvcc.Log) (Perm : Int → IProp GF)
    (R : mvcc.Log) (r : mvcc.CmpRecs) (RC : IProp GF) (Ls : List w64)
    (hk : Option val) (Pre Q Post X Y : IProp GF) (dq : DFrac),
  {{ ⌜mvcc.batchLimitOk cfg.CompactionBatchLimit' ∧ mvcc.restoreLogOk R⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        ∃ Dep : IProp GF, mvcc.isKeyBackendGR b (mvcc.bucketView γ) (mvcc.storeRT γ)
          (mvcc.storeWT γ) (mvcc.kbRecs γ.kb γ.bucket r) r (mvcc.storePutOk γ) (mvcc.delKey γ)
          (mvcc.storeW s γ) (mvcc.kbWi γ.kb) Dep (mvcc.storeCmp γ) P (mvcc.hookFn γ)
          (mvcc.storeReq γ) (mvcc.storeRb γ) (mvcc.storeBt γ) (mvcc.kbSR γ.kb) (mvcc.kbSRh γ.kb)
          (mvcc.kbMWv γ.kb γ.bucket) (mvcc.kbHookNilAt γ.kb)) ∗
      (∀ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanReadR b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ RC)
          (mvcc.kbRecs γ.kb γ.bucket r) r) ∗ RC ∗
      mvcc.restoreImageM d γb ([[], []] ++ R) r ∗ mvcc.restoreRcptM d ([[], []] ++ R) ∗
      mvcc.kbNoDelOff (some d) ∗ mvcc.kbRegRight (some d) ∗
      mvcc.kbWT (some d) ∗ mvcc.kbWT (some d) ∗ mvcc.kbSRM (some d) ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d)) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl Ls ∅ ∗
      ⌜∀ it lid, (mvcc.pendItems ([[], []] ++ R) []).lookup it = some lid →
        lid ∈ Ls ∧ (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 M ∗
      (⌜([[], []] ++ R).length ≤ 2⌝ ∨ (W64 (([[], []] ++ R).length : Int)) ↪[γok]□ ([[], []] ++ R) ∨
        (W64 0) ↪[γok]□ ([] : mvcc.Log)) ∗
      (⌜r.finRev = -1⌝ ∨ □ Perm r.finRev) ∗ (⌜r.crev = -1⌝ ∨ □ Perm r.crev) ∗
      mvcc.resumeCtxM d r P hk Pre Q Post dq X Y ∗
      (if r.resumes then mvcc.kbWTSupplyM (some d) else iprop(True)) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #s);
      ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧
        γ.st.kb = some d ∧ γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag ∧ γ.st.cm = d.cm⌝ ∗
        mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ ∗
          mvcc.rdCalls rd (go.GoType.PointerType watchableStore.ty) #s) ∗ mvcc.hookP γ.st P ∗
        mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 M ∗
        ([∗list] _x ∈ List.replicate (mvcc.nReaders - mvcc.nJobRd (some d) - 2) (),
          mvcc.watchReader s st γ) ∗
        mvcc.wsCloserM s st γ.st r.crev ∗
        mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd (some d)) ∗
        mvcc.crevPermIs γ.st Perm ∗
        mvcc.writerReg st γ.st ∗
        mvcc.api.newClient γ.st.api ([[], []] ++ R) r.crev (1 : Qp).half st ∗
        lease.leaseOwn γl Ls (mvcc.pendItems ([[], []] ++ R) []) ∗ RC ∗
        mvcc.resumeBackM d r hk dq Post Y ∗ £ 1 }}

/-- **Today's `New.spec` as an instance**: as `NewStore.spec_of_specR`, not exact (the real backend
only; the clean view and read with `RC`; the lessor's part lent; the image's tracked values); the
post exactly today's off (`wsCloserM_off`, `crevRightM_off`), on with `wsCloserR … (-1)` in place of
`wsCloser ∗ crevRightM`, which `NewApi` makes at once (`compactRightR_of_closer`). -/
theorem mvcc.New.spec_of_specR (h : mvcc.New.specR (GF := GF) (hG := hG))
    [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (b le : GoInterface) (cfg : StoreConfig)
    (d : mvcc.KBReal) (γb γl : GName) (P : IProp GF) (rd0 : GoFunc)
    (γi : mvcc.IdxNames) (γok γtag : GName) (Perm : Int → IProp GF) (RC : IProp GF)
    (hcfg : mvcc.batchLimitOk cfg.CompactionBatchLimit') :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.storeBackend b s γ P) ∗
      (∀ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanRead b (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ RC)
          (mvcc.kbNoCmpF γ.kb γ.bucket)) ∗ RC ∗
      mvcc.restoreImageM d γb [[], []] mvcc.CmpRecs.empty ∗
      mvcc.kbNoDelOff (some d) ∗ mvcc.kbRegRight (some d) ∗ mvcc.kbWT (some d) ∗
      mvcc.kbWT (some d) ∗ mvcc.kbSRM (some d) ∗
      ([∗list] _x ∈ List.replicate mvcc.nReaders (), mvcc.kbRT (some d)) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      lease.leaseOwn γl [] ∅ ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #s);
      ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧
        γ.st.kb = some d ∧ γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag ∧
        γ.st.cm = decide (mvcc.kbCmpM (some d))⌝ ∗
        mvcc.isWatchableStore s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ ∗
          mvcc.rdCalls rd (go.GoType.PointerType watchableStore.ty) #s) ∗
        mvcc.hookInit γ.st P #func.nil ∗
        mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        ([∗list] _x ∈ List.replicate (mvcc.nReaders - mvcc.nJobRd (some d) - 2) (),
          mvcc.watchReader s st γ) ∗
        mvcc.wsCloserM s st γ.st (-1) ∗
        mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd (some d)) ∗
        mvcc.crevPermIs γ.st Perm ∗
        mvcc.writerReg st γ.st ∗ mvcc.api.newClient γ.st.api [[], []] (-1) (1 : Qp).half st ∗
        lease.leaseOwn γl [] ∅ ∗ RC ∗ £ 1 }} := by
  sorry

end spec

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **R1's bridge lemma** (review round 1's F2.1; to prove in Probe, `sorry` until then): the
records' clean read of a compacting real backend (`cm` on) **after** the store's deletable keys are
fixed (`storeDlReg d.γB γi`, which `NewStore`'s batch session needs before `restore()`), lent with a
reader's token the client's half of the deleted entries at none (`backend.dlsOwn d.γB ∅`, the part of
`restoreImageM`'s `kbVals … ∅` that pins "nothing deleted since the open"), in place of
`keyCleanRead_of_backendC`'s unfixed `dlInit` (consumed by the fix). Its premises are what the glue
holds when it calls `NewStore` (`mvccStorageFor` opened: `isBackend`, `keySized`, `bridgeParams`,
`recsSign r` from the image; the registration fixed at step 2). Off (`cm` false) nothing new is
needed: `keyCleanRead_of_backend` with `dlNoDel` (`kbNoDelOff`), `r = empty`.

Why it should hold: the clean read's argument (`bridge_rt_cleanR`, `rt_lockedR`) uses `dlInit`'s flag
at `false` only to know that the read buffer and the committed data have no deleted safe-range
entry the view lacks; with the registration fixed, a delete is possible in principle, but every
delete updates the deleted entries' ghost (`γ.dls`, both halves: `dlsOwn`'s other half is the batch
lock's), so the client's half at `∅`, lent to the read, pins it at none for the read's duration.
If this fails, the fallback is R1's other branch (`notes/mvccfull-proof-plan.md`, B3's risk R1). -/
theorem mvcc.NewStore.cleanRead_of_image
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hrRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hrRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hrUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (d : mvcc.KBReal) (hP : mvcc.bridgeParams d.P) (hcm : d.cm = true) (Pk : IProp GF)
    (γb : GName) (γi : mvcc.IdxNames) (r : mvcc.CmpRecs) (hpos : mvcc.recsSign r) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend d.γB d.P (mvcc.lateW d.gx) Pk d.be ∗ mvcc.keySized d.γB d.P d.be ∗
      mvcc.storeDlReg d.γB γi ⊢
      ∀ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.kb = some d ∧ γ.idx = γi⌝ →
        mvcc.keyCleanReadR
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be) (mvcc.bucketViewC γ) iprop(mvcc.storeRT γ ∗ backend.dlsOwn d.γB ∅)
          (mvcc.kbRecs γ.kb γ.bucket r) r := by
  sorry

/-- **The API's candidate from the internal one** (the bridge `Restore`'s API proof uses). Outline,
in the order of `NewApi.lean`'s `New.wp_proof`, with `RestoreApi.lean`'s bridge in place of
`imageOk_start`:

1. `mvccStorageFor B Pk σ.log σ.crev u` opened as `restore_of_storage` does: `bk`, `D`, the image
   `imageOk D σ.log σ.crev u` (`snap.imageOk_keyImageM`: records `r` with `r.crev = σ.crev`,
   `r.resumes = u`, `keyImageM true σ.log r D`), `σ.log = [[], []] ++ R` with `restoreLogOk R`
   (`restoreLog_ch`, the `IdxWf` from `LogB`/`LogWf'`), `recsSign r`, the receipt `⧖ (logCh σ.log)`
   (→ `restoreRcptM bk σ.log`, mode on). `restore_of_storage` is `private` and quantifies over
   `γ.withPhys p` for a given `γ`; its body is what is reused, at `∀ γ` with `γ.idx = γi`.
2. The index's names `γi` (`idxFresh_alloc`) first, then the registration fixed at them
   (`storeDlReg_fix bk.γB γi`, consuming `dlInit`), as `NewApi` today; the contract at the records
   (`storeBackendTR_of_backendC … γi r hsign`, needing `fkV … true`, from `fkV_of_fkCl` with
   `fkWfD_of_keyImageM`) gives the first conjunct (`Dep := True`).
3. The image `restoreImageM bk γb σ.log r` from `restoreImageM_of_openOn` (`bView` and `fkCl`).
4. The clean read: NOT `keyCleanRead_of_backendC` (it lends `dlInit`, consumed in 2): R1's bridge
   lemma `mvcc.NewStore.cleanRead_of_image` above, over the fixed registration, lent
   `backend.dlsOwn bk.γB ∅`, which `restoreImageM`'s `kbVals … ∅` carries. So `RC` cannot be both
   lent to the read and inside the whole `restoreImageM` the pre also takes (review round 1's
   F2.1): the internal `NewStore.specR` is restated once the lemma is proved (`NewStoreR.lean`'s
   header, "R1"). (`RC := dlInit` with step 2 postponed is impossible: `NewStore`'s batch session
   needs the contract.)
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
theorem mvcc.api.New.specR_of_internal
    (hNew : mvcc.New.specR (GF := GF) (hG := hG))
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
    mvcc.api.New.specR (GF := GF) (hG := hG) := by
  sorry

end glue

end EtcdGrove
end Perennial
