/-
`store.restore` (`kvstore.go`), over a `Key` bucket with data (D22 S-g), a compaction job may
have thinned (M2, the storage side, item 18).
Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.IdxPriv
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreRecs

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

/-- `s.restore()` over a backend whose `Key` bucket holds the entries `ents` of the restored log
`L' = [[], []] ++ R` (`restoreLogOk R`: every revision of `R` with changes, the log well formed, no
lease) a compaction job left at the restored revision, with the image's compaction records `r`
(M2, the storage side, item 18, 2026-10-30), read-only: `NewStore` restores the empty bucket
(`R = []`), `store.Restore` a snapshot's (the restore plan's R4, R5c), returning `nil`. It reads
with a `ReadTx` (a reader's token `RT`, given back): for a bucket with data, over a clean read
buffer (`restoreViewR`: the store's clean view of the image's bucket `bucketOfEnts ents` and the
backend's clean-view `ReadTx` at the records, `keyCleanReadR`), where a limited range returns the
range's first entries (`issues/etcd-unsafe-range-limit-buffer.md`).

* **The image** (`entsCutAt L' r.crev ents`): the log's entries but, per key, a prefix deletable by
  the compaction at the restored revision `r.crev` (`CmpRecs.crev`: the scheduled record if
  `restore()` resumes it, else the finished one, else `-1`); the whole bucket at no record
  (`entsCutAt_full`). The records are of `L'` (`recsOk`), read through the records' resource `NC`
  (the backend's compaction-key flag as opened, `kbRecs` at the store; `kbNoCmp` at no record),
  which `restore` gives back.
* **The index** is rebuilt while private (`ownIdxPriv`, as `newTreeIndex` returns it:
  `restoreIntoIndex`'s goroutine updates key indexes outside the tree's lock, the restore plan's
  R3 design point), the bucket read in chunks of `restoreChunkKeys` entries and sent to the
  goroutine, then made a lock-protected index (`isTreeIndex`, with every reader's token:
  `idx_publishAt`) at `L'` and the compaction level `r.crev` (`IdxCRepN`, each key cut at its first
  surviving revision: `idxRestore_cut`), from the lock's ghost part at that level (`idxLockGAt`)
  and the writer's handle's lower bounds there (`idxWriterLb`: the caller keeps the handle), with a
  receipt per entry the rebuild took (`ents.length`).
* **`compactMainRev`** is stored the finished record, if any, under `s.revMu`'s first round
  (`revFinW`: the lock's part `dql` of it, which with `restore`'s part `dqc` makes the whole when
  there is a record).
* **`currentRev`** is stored the last revision, `|L'| - 1` (the rebuild's answer raised to the two
  records, `restoreCur_cut`), under `s.revMu`'s second round: the caller gives the lock's
  protocol, `RevP` before, its part `q2` of `currentRev` (at `1`) with `RevK` once locked, `RevQ`
  once unlocked with it at `|L'| - 1`, the view `restore` read through, the index's lock with every
  reader's token and the restored log's changes below the time receipts' bound (from the rebuild's
  receipts for the whole bucket, else the caller's premise); `restore` holds the other part `q1`.
* **The resumed compaction** (`resumeK`): if the records resume one (`CmpRecs.resumes`),
  `compactLockfree` at the scheduled record, from what `restore` has then (`restoreDone`), as the
  caller provides it; `restore` ends in the caller's `Fin`.
* **No lease** is attached (`keyToLease` stays empty: no entry has a lease).

At no record, the whole bucket, `RevP0 = RevP` and `Fin` the post, today's text before item 18
(`store.restore.specNC`, `store.restore.specNC_of_spec`). -/
abbrev mvcc.store.restore.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q : Qp) (P : IProp GF)
    (HF : val → IProp GF) (RT WT W Wi Dep NC : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop)
    (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (MW SR SRh : IProp GF)
    (dqb dqi : DFrac)
    (R : mvcc.Log) (RevP0 RevP RevK RevQ : IProp GF) (dqc dql : DFrac) (q1 q2 : Qp)
    (r : mvcc.CmpRecs) (ents : List mvcc.KvEnt) (Fin : IProp GF),
  mvcc.restoreLogOk R → q1 + q2 = 1 → mvcc.recsOk ([[], []] ++ R) r →
    (∀ x, r.fin = some x → dqc • dql = DFrac.own 1) →
    mvcc.entsCutAt ([[], []] ++ R) r.crev ents →
    (ents = mvcc.logEnts ([[], []] ++ R) 0 ([[], []] ++ R).length ∨
      mvcc.logCh ([[], []] ++ R) < receiptBound GF) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦{dqb} b ∗
      mvcc.isKeyBackendGR b (mvcc.bucketView γ) RT WT NC r PutOk (mvcc.delKey γ) W Wi Dep Cmp P HF
        (Rb := Rb) (Bt := Bt) (SR := SR) (SRh := SRh) (MW := MW) ∗
      RT ∗ NC ∗ mvcc.restoreViewR b γ RT q R (mvcc.bucketOfEnts ents) NC r ∗
      s.[store, go!"kvindex"] ↦{dqi}
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockGAt γ.idx (mvcc.evsOf (([[], []] ++ R) ++ [[]])).length r.crev ∗
      mvcc.idxWriterLb γ.idx ([[], []] ++ R) ∗
      s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own q1} (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦{dqc} (W64 (-1) : w64) ∗ RevP0 ∗
      mvcc.revFinW s dql r.fin RevP0 RevP ∗
      mvcc.revLockW s q2 RevP RevK ∗
      mvcc.revUnlockW s q2 ([[], []] ++ R) RevK
        iprop((if R = [] then mvcc.bucketView γ q ∅ else mvcc.bucketViewC γ q (mvcc.bucketOfEnts ents)) ∗
          mvcc.isTreeIndex ti γ.idx ∗
          ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
            mvcc.idxReader ti γ.idx) ∗
          ⌜mvcc.logCh ([[], []] ++ R) < receiptBound GF⌝) RevQ ∗
      mvcc.resumeK s r
        (mvcc.restoreDone s b ti q1 dqb dqi dqc ([[], []] ++ R) ents r RT NC RevQ) Fin }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; Fin }}

end spec

end EtcdGrove
end Perennial
