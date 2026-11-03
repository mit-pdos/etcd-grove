/-
**`store.Restore` in compaction mode: the resources of `restore()`'s rounds** (M2's item 15, step A3;
`notes/m2-storage-plan.md`, "Step 2: restore in compaction mode"): what `store.Restore`'s proof
(`store__Restore.lean`, its compaction-mode branch) passes to `store.restore` for its `s.revMu`
rounds, the switch and its end.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreCmp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]


/-! ## The resources of `restore()`'s rounds, in compaction mode -/

/-- `restore()`'s first `s.revMu` round's resource (the restoring flag's half, later credits and
the kept quarter of `compactMainRev`, at `-1`). -/
def mvcc.restoreOnP0 (s : Loc) (γ : mvcc.StoreNames) : IProp GF :=
  iprop(dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ £ 1 ∗ £ 1 ∗ £ 1 ∗
    (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (W64 (-1) : w64) : IProp GF))

/-- The second round's (the kept quarter at the finished record `x`). -/
def mvcc.restoreOnP (s : Loc) (γ : mvcc.StoreNames) (x : w64) : IProp GF :=
  iprop(dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ £ 1 ∗ £ 1 ∗
    (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} x : IProp GF))

/-- What the second round holds between its lock and its unlock. -/
def mvcc.restoreOnK (s : Loc) (γ : mvcc.StoreNames) (x : w64) : IProp GF :=
  iprop(sync.ownRWMutexWLocked (mvcc.revMuAddr s) (mvcc.revMuInv s γ) ∗
    dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗ dghostVar γ.rst (DFrac.own (1 : Qp).half) true ∗
    (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half} x : IProp GF) ∗
    (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} x : IProp GF) ∗ £ 1)

/-- What the restore keeps of the caller's through `restore()`: the revision tokens not spent at the
restored log, the outer quarter of the committed log's authority (a watchable store's) and the old
pool's readers but the writer's and the job's. -/
def mvcc.restoreOnRest (γ : mvcc.StoreNames) (R : mvcc.Log) : IProp GF :=
  iprop(ownToks γ.revs (2 ^ 63 - 3 - ([[], []] ++ R).length) ∗
    (if γ.watchQ then mvcc.logQ γ ([[], []] ++ R) else iprop(True)) ∗
    ([∗list] _x ∈ List.replicate (mvcc.nReaders - 3) (), mvcc.storeRT γ))

/-- What the switch leaves (`restore_switch`'s post but `s.revMu`'s resource, with the kept quarter
of `compactMainRev`, the lag's rest, the new index and the restored log's certificate). -/
def mvcc.restoreOnQ (s : Loc) (γ : mvcc.StoreNames) (p' : mvcc.PhysNames) (o' : mvcc.StoreObjs)
    (R : mvcc.Log) (r : mvcc.CmpRecs) (ti : Loc) : IProp GF :=
  iprop(dghostVar γ.rst (DFrac.own (1 : Qp).half) false ∗
    mvcc.curAt (γ.withPhys p') (DFrac.own (1 : Qp).half) o' ∗ mvcc.writerFrag (γ.withPhys p') ∗
    mvcc.curAt (γ.withPhys p') (DFrac.own (1 : Qp).half.half.half) o' ∗
    mvcc.retiredAt γ 3 ∗ ghostVar γ.wsd (1 : Qp).half () ∗ mvcc.restoreWriter γ ([[], []] ++ R) ∗
    mvcc.restoreOnRest γ R ∗
    (if r.finRev = r.crev then ghostVar γ.wsd (1 : Qp).half.half () else iprop(True)) ∗
    (s.[store, go!"compactMainRev"] ↦{DFrac.own (1 : Qp).half.half} (r.fin.getD (W64 (-1))) :
      IProp GF) ∗
    mvcc.isTreeIndex ti (γ.withPhys p').idx ∗ mvcc.idxCert γ.idx ([[], []] ++ R))

/-- The store at the new names once `restore()` is done, before its resumed compaction: `s.mu`'s
resource with the lag, the new compaction right, and what the switch left. -/
def mvcc.restoreOnReady (s : Loc) (γ : mvcc.StoreNames) (p' : mvcc.PhysNames) (o' : mvcc.StoreObjs)
    (R : mvcc.Log) (r : mvcc.CmpRecs) : IProp GF :=
  iprop(mvcc.muInvLag s (γ.withPhys p') r.crev r.finRev ∗ mvcc.compactRightR s (γ.withPhys p') r.crev ∗
    mvcc.storeRT (γ.withPhys p') ∗ mvcc.writerFrag (γ.withPhys p') ∗ ghostVar γ.wr 1 () ∗
    mvcc.fieldShareAt s (γ.withPhys p') (1 : Qp).half o' ∗
    mvcc.fieldShareAt s (γ.withPhys p') (1 : Qp).half.half o' ∗
    mvcc.retiredAt γ 3 ∗ ghostVar γ.wsd (1 : Qp).half () ∗
    mvcc.restoreOnRest γ R ∗
    (if r.finRev = r.crev then ghostVar γ.wsd (1 : Qp).half.half () else iprop(True)) ∗
    mvcc.idxCert γ.idx ([[], []] ++ R))

/-- `restore()`'s end (after its resumed compaction, if any). -/
def mvcc.restoreOnFin (s : Loc) (γ : mvcc.StoreNames) (p' : mvcc.PhysNames) (o' : mvcc.StoreObjs)
    (d' : mvcc.KBReal) (R : mvcc.Log) (r : mvcc.CmpRecs) : IProp GF :=
  iprop(|={⊤}=> (mvcc.muInvAt s (γ.withPhys p') 1 r.crev ∗ ghostVar γ.wr 1 () ∗
    mvcc.fieldShareAt s (γ.withPhys p') (1 : Qp).half o' ∗ mvcc.compactRightR s (γ.withPhys p') r.crev ∗
    mvcc.fieldShareAt s (γ.withPhys p') (1 : Qp).half.half o' ∗
    mvcc.storeRT (γ.withPhys p') ∗ mvcc.writerFrag (γ.withPhys p') ∗ mvcc.resumeHookM d' r ∗
    ghostVar γ.wsd (1 : Qp).half.half () ∗ mvcc.retiredAt γ 3 ∗ ghostVar γ.wsd (1 : Qp).half () ∗
    mvcc.restoreOnRest γ R ∗
    mvcc.idxCert γ.idx ([[], []] ++ R)))

end defs

end EtcdGrove
end Perennial
