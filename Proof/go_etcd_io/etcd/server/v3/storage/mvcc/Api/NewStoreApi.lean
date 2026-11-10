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

/-- **`NewStore.spec`** (the API's) from the internal one and the bridge's backend specs (B3 Prove:
the proof of the fresh statement, until mvccfull's Freeze of 2026-11-10, is at commit `ae30739dde`;
the outline is `New.wp_proof`'s, `NewApi.lean`, at a store without watchers; review round 2's S3/S4:
its glue, `restore_of_storage`'s reuse, is written here). -/
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
  -- B3 Prove (mvccfull's Freeze, 2026-11-10): as `New.wp_proof` (`NewApi.lean`), over the internal
  -- `mvcc.NewStore.spec` (also restated).
  sorry

end proof

end api
end mvcc
end EtcdGrove
end Perennial
