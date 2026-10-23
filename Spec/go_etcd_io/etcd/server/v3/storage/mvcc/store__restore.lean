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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.restore()` over an empty `Key` bucket (`bucketView γ q ∅`, read-only): what `NewStore`
restores, with `s.mu` held, after creating the buckets (the restore plan's R4, option 1: a bucket
with data, as `store.Restore` restores, waits on two extensions of the backend's contract,
`notes/restore-plan.md`, R4b and R4d), returning `nil`. It reads with a `ReadTx` (a reader's
token `RT`, given back).

* **The index** is rebuilt (nothing to put) while private (`ownIdxPriv`, as `newTreeIndex` returns
  it: `restoreIntoIndex`'s goroutine updates key indexes outside the tree's lock, the restore
  plan's R3 design point), then made a lock-protected index (`isTreeIndex`, with every reader's
  token: `idx_publish`) at the log `[[], []]`, from the lock's ghost part (`idxLockG`) and the
  writer's handle there (given back).
* **`currentRev`** is stored the last revision seen, `1` (`restoreIntoIndex` sends it through its
  channel), under `s.revMu`, locked and unlocked while it is private memory (back at its zero
  value, `PlainRWMutex.lean`); the whole of `currentRev` is taken.
* **No compaction** is found (`kbNoCmp`, the backend records none, consumed: its reads of the
  compaction keys find nothing, `kbNoCmp_metaNone`, the trust boundary): `compactMainRev` stays
  `-1` and no compaction is resumed.
* **No lease** is attached (`keyToLease` stays empty: no entry is read). -/
abbrev mvcc.store.restore.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q : Qp) (P : IProp GF)
    (HF : val → IProp GF) (RT WT W Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop) (dqb dqi : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      mvcc.isKeyBackendG b (mvcc.bucketView γ) RT WT PutOk (mvcc.delKey γ) W Wi Dep Cmp P HF ∗
      RT ∗ mvcc.kbNoCmp γ.kb γ.bucket ∗ mvcc.bucketView γ q (∅ : mvcc.Bucket) ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockG γ.idx 0 ∗ mvcc.idxWriter γ.idx [[], []] [] ∗
      s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦ (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) ∗
      s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; mvcc.bucketView γ q (∅ : mvcc.Bucket) ∗ RT ∗
      mvcc.isTreeIndex ti γ.idx ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.idxReader ti γ.idx) ∗
      mvcc.idxWriter γ.idx [[], []] [] ∗
      s.[store, go!"currentRev"] ↦ (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) ∗
      s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) }}

end spec

end EtcdGrove
end Perennial
