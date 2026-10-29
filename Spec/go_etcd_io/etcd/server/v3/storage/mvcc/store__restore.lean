/-
`store.restore` (`kvstore.go`): the trust boundary (translated 2026-10-23, `notes/restore-plan.md` R0; not yet proved), over a `Key` bucket with data
(D22 S-g).
Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.IdxPriv
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

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

/-- `s.restore()` over a backend whose `Key` bucket holds the restored log `L' = [[], []] ++ R`
(`restoreLogOk R`: every revision of `R` with changes, the log well formed, no lease), read-only:
`NewStore` restores the empty bucket (`R = []`), `store.Restore` a snapshot's (the restore plan's
R4, R5c), returning `nil`. It reads with a `ReadTx` (a reader's token `RT`, given back): for a
bucket with data, over a clean read buffer (`restoreView`: the store's clean view and the
backend's clean-view `ReadTx`, `keyCleanRead`), where a limited range returns the range's first
entries (`issues/etcd-unsafe-range-limit-buffer.md`: with entries in the read buffer it may skip
some).

* **The index** is rebuilt while private (`ownIdxPriv`, as `newTreeIndex` returns it:
  `restoreIntoIndex`'s goroutine updates key indexes outside the tree's lock, the restore plan's
  R3 design point), the bucket read in chunks of `restoreChunkKeys` entries and sent to the
  goroutine, which reads their keys (a share of the read transaction, `rdSplit`) and answers the
  last revision, then made a lock-protected index (`isTreeIndex`, with every reader's token:
  `idx_publish`) at `L'`, from the lock's ghost part (`idxLockG`) and the writer's handle there
  (its handle's lower bounds, `idxWriterLb`: the caller keeps the handle), with a receipt per change
  (the goroutine's steps put each entry, one per change, `logEnts_length`).
* **`currentRev`** is stored the last revision, `|L'| - 1` (what the goroutine answers: every
  revision of `R` has an entry), under `s.revMu`, which `restore` locks once: the caller gives the
  lock's protocol, `RevP` before, its part `q2` of `currentRev` (at `1`) with `RevK` once locked,
  `RevQ` once unlocked with it at `|L'| - 1`, the view `restore` read through (idle after its
  `RLock`), the index's lock with every reader's token (made before: `store.Restore` refills its
  readers' pool from them there) and the restored log's changes below the time receipts' bound (the
  rebuild's receipts: `store.Restore` certifies `L'` there); `restore` holds the other part `q1` and a part of
  `compactMainRev` (`-1`), which it reads outside the lock too (`NewStore`:
  private memory, `PlainRWMutex.lean`; `store.Restore`: the lock in restoring mode, the restore
  plan's R5e).
* **No compaction** is found (`kbNoCmp`, the backend records none, consumed: its reads of the
  compaction keys find nothing, the read transaction's clause under it, `keyReadLocked_meta`; until
  the backend-compaction stage, 2026-10-29, the axiom `kbNoCmp_metaNone`): `compactMainRev` stays
  `-1` and no compaction is resumed.
* **No lease** is attached (`keyToLease` stays empty: no entry has a lease). -/
abbrev mvcc.store.restore.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q : Qp) (P : IProp GF)
    (HF : val → IProp GF) (RT WT W Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop) (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (MW SR SRh : IProp GF)
    (dqb dqi : DFrac)
    (R : mvcc.Log) (RevP RevK RevQ : IProp GF) (dqc : DFrac) (q1 q2 : Qp),
  mvcc.restoreLogOk R → q1 + q2 = 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      mvcc.isKeyBackendG b (mvcc.bucketView γ) RT WT (mvcc.kbNoCmp γ.kb γ.bucket) PutOk (mvcc.delKey γ) W Wi Dep
        Cmp P HF (Rb := Rb) (Bt := Bt) (SR := SR) (SRh := SRh) (MW := MW) ∗
      RT ∗ mvcc.kbNoCmp γ.kb γ.bucket ∗ mvcc.restoreView b γ RT q R ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockG γ.idx (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length ∗
      mvcc.idxWriterLb γ.idx ([[], []] ++ R) ∗
      s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗ RevP ∗
      mvcc.revLockW s q2 RevP RevK ∗
      mvcc.revUnlockW s q2 ([[], []] ++ R) RevK
        iprop(mvcc.restoreViewOut γ q R ∗ mvcc.isTreeIndex ti γ.idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti γ.idx) ∗
          ⌜mvcc.logCh ([[], []] ++ R) < receiptBound GF⌝) RevQ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; RT ∗ mvcc.kbMW γ.kb γ.bucket ∗
      ⧗ (mvcc.logCh ([[], []] ++ R)) ∗ RevQ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 ((([[], []] ++ R).length : Int) - 1) : w64) ∗
      s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) }}

end spec

end EtcdGrove
end Perennial
