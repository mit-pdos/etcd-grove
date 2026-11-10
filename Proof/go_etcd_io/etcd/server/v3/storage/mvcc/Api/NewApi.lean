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

/-- **`New.spec`** (the API's) from the internal one and the bridge's backend specs (B3 Prove: the
proof of the fresh statement, until mvccfull's Freeze of 2026-11-10, is at commit `ae30739dde`).
Outline (the bridge `Restore`'s API proof uses),
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
  -- B3 Prove (mvccfull's Freeze, 2026-11-10): the outline above, over the internal `mvcc.New.spec`
  -- (also restated); `NewStoreRCallers.lean`'s `backendC_newStoreR_pre` gives its backend part.
  sorry

end proof

end api
end mvcc
end EtcdGrove
end Perennial
