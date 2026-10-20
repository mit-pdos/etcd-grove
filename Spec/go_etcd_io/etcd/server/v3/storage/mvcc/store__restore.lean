/-
`store.restore` (`kvstore.go`): the trust boundary (untranslated), over a `Key` bucket with data
(D22 S-g).
Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.restore()` (`NewStore` calls it with `s.mu` held, after creating the buckets; `Restore` with
`s.mu` held, after installing a new backend, index and scheduler) over a `Key` bucket holding the
log `[[], []] ++ R` (`bucketView γ q (bucketMap _)`, read-only; D22 S-g, 2026-10-19: until then
only an empty bucket, `R = []`), returning `nil`.

* **The index** (`isTreeIndex ti γ.idx`, empty) is rebuilt from the bucket (`restoreIntoIndex`,
  per change): `restoreIdxPre`/`restoreIdxPost`, the writer's handle at the log `[[], []] ++ R`
  with a time receipt per change (D22h restated: `restore`'s own steps pay for the image's
  changes). With `R = []` the bucket is empty, nothing is read and the index is not touched.
* **`currentRev`** is stored the last revision seen (`restoreIntoIndex` sends it through its
  channel; `1` if none: the log's last, as every revision of `R` has an entry, `restoreLogOk`),
  under `s.revMu`, locked and unlocked fresh (back at its zero value). With `R = []` the store of
  `1` is modelled as no write and `NewStore` holds only half of `currentRev` here (`qc`; the
  batch lock holds the other half since `NewStore`'s first `tx.Unlock()`, as the writers'
  resource; in the code the write is protected by `s.mu` held exclusively, which the model's
  `s.mu`, holding nothing, does not express); with data the write changes the value, so the
  whole of it is taken.
* **No compaction** is found (`kbNoCmp`, the backend records none: D19l (v) (A), in place of the
  opaque premise `backendNoCompaction`; consumed): `compactMainRev` stays `-1` and no compaction
  is resumed (`compactLockfree` is not called). An unfinished compaction (scheduled above the
  finished one) is excluded, not resumed: resuming schedules a compaction job on the store's
  scheduler, which needs the compaction right (`compactRight`) and a backend that supports the
  compaction's calls (`storeCmp`, false of the real backend), and the server's workload never
  compacts (S-f's `keyImage` has neither key).
* **No lease** is attached (`restoreLogOk`: no put with a lease, so `keyToLease` stays empty and
  `s.le` is not called). -/
abbrev mvcc.store.restore.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q qc : Qp) (P : IProp GF)
    (HF : val → IProp GF) (RT WT W Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop) (R : mvcc.Log),
  mvcc.restoreLogOk R → (R.isEmpty = false → qc = 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦□ b ∗
      mvcc.isKeyBackendG b (mvcc.bucketView γ) RT WT PutOk (mvcc.delKey γ) W Wi Dep Cmp P HF ∗
      mvcc.kbNoCmp γ.kb γ.bucket ∗
      mvcc.bucketView γ q (mvcc.bucketMap ([[], []] ++ R)) ∗
      s.[store, go!"kvindex"] ↦□
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.isTreeIndex ti γ.idx ∗ mvcc.restoreIdxPre γ.idx R ∗
      s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own qc} (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) ∗
      s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; mvcc.bucketView γ q (mvcc.bucketMap ([[], []] ++ R)) ∗
      mvcc.restoreIdxPost γ.idx R ∗
      s.[store, go!"currentRev"] ↦{DFrac.own qc}
        (W64 (((([[], []] ++ R).length : Nat) : Int) - 1) : w64) ∗
      s.[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) ∗
      s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) }}

end spec

end EtcdGrove
end Perennial
