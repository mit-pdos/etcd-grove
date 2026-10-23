/-
`store.restore` (`kvstore.go`): the trust boundary (translated 2026-10-23, `notes/restore-plan.md` R0; not yet proved), over a `Key` bucket with data
(D22 S-g).
Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.IdxPriv

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

* **The index** is rebuilt from the bucket (`restoreIntoIndex`, per change) while it is private
  (`ownIdxPriv`, as `newTreeIndex` returns it: the goroutine updates key indexes outside the tree's
  lock; the restore plan's R3 design point), then made a lock-protected index (`isTreeIndex`,
  with every reader's token: `idx_publish`) at the log `[[], []] ++ R`: the lock's ghost part
  (`idxLockG`), the writer's handle and the caller's half of the committed log's authority, at
  `[[], []]`, come back at that log, with its certificate; the handle holds a time receipt per
  change (D22h restated: `restore`'s own steps pay for the image's changes, one per entry the
  goroutine takes).
* **`currentRev`** is stored the last revision seen (`restoreIntoIndex` sends it through its
  channel; `1` if none: the log's last, as every revision of `R` has an entry, `restoreLogOk`),
  under `s.revMu`, locked and unlocked while it is private memory (back at its zero value,
  `PlainRWMutex.lean`); the whole of `currentRev` is taken (until 2026-10-23, with `R = []`, only
  half, the store of `1` modelled as no write: unprovable, `notes/restore-plan.md`, R4).
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
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q : Qp) (P : IProp GF)
    (HF : val → IProp GF) (RT WT W Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop) (R : mvcc.Log)
    (dqb dqi : DFrac),
  mvcc.restoreLogOk R →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      mvcc.isKeyBackendG b (mvcc.bucketView γ) RT WT PutOk (mvcc.delKey γ) W Wi Dep Cmp P HF ∗
      mvcc.kbNoCmp γ.kb γ.bucket ∗
      mvcc.bucketView γ q (mvcc.bucketMap ([[], []] ++ R)) ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockG γ.idx 0 ∗ mvcc.idxWriter γ.idx [[], []] [] ∗
      mvcc.idxLogAuth γ.idx (1 : Qp).half [[], []] ∗
      s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦ (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) ∗
      s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; mvcc.bucketView γ q (mvcc.bucketMap ([[], []] ++ R)) ∗
      mvcc.isTreeIndex ti γ.idx ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.idxReader ti γ.idx) ∗
      mvcc.idxWriter γ.idx ([[], []] ++ R) [] ∗ mvcc.idxLogAuth γ.idx (1 : Qp).half ([[], []] ++ R) ∗
      mvcc.idxCert γ.idx ([[], []] ++ R) ∗
      s.[store, go!"currentRev"] ↦ (W64 (((([[], []] ++ R).length : Nat) : Int) - 1) : w64) ∗
      s.[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) ∗
      s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) }}

end spec

end EtcdGrove
end Perennial
