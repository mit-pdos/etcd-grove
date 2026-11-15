/-
`(*store).scheduleCompaction(compactMainRev, prevCompactRev)` (`kvstore_compaction.go:28`).
Internal: the compaction job's body (`compact`'s closure).

**Proof sketch**: `LockForSafeRangeDelete` (the job's `kbSafe`, in `compactJobRes`);
`kvindex.Compact(rev)` (the index compacted at `rev`, `idxCompact`, its available revisions
`idxCompactAvail`); per batch: `LockOutsideApply` (no hook; the job's open share `kbOpen`, in
`compactJobRes`), `UnsafeRange` of `Key` below `rev+1` (the batch's `KeyData.range`; its bytes lent
against half the session's liveness `kbLive`, which the batch's writes do not need),
`UnsafeDelete` of every entry not available, passing the lent key bytes themselves (each a key
committed before this session and not yet deleted in it: the row's `D.keys k = D0.keys k`; the
store's image stays an image of the committed history with an unfinished compaction, `mvccImage …
true`), `WriteKeyValue` of each (keys parse: the image's), the lent bytes back (`kbLive B tx 1`),
then the last batch's `UnsafeSetFinishedCompact` (image complete again, `u = false`; the entry bound
trivial) and `Unlock` (the job's nested update: the finished key at the write-back, the batch's
deletes at its commit, 4a's F1), or `Unlock`, `ForceCommit` (`storageReq_true`, the open share) and a
sleep or the stop channel (`storeStopped` on that branch). The job's resources go back to the store's invariant at its end.
`CompactionBatchLimit ≥ 0` (`storeCfgOk`): with a negative one the loop never ends (no panic).

**Changes** from `specs-ref`'s file: over `compactJobRes`; the outcomes only (the hash's fields).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.scheduleCompaction(rev, prev)` with the job's resources: the compaction's hash of the
revisions `(prev, rev]`, or (stopped) an error. -/
def store.scheduleCompaction.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (rev prev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ isStore s γ ∗
      compactJobRes s γ rev prev ∗ schemaVars }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"scheduleCompaction")) (Val #rev))
      (Val #prev))
  {{ (h : KeyValueHash) (err : GoInterface), RET (PairV #h #err);
      ⌜err = GoInterface.nil ∧ h.CompactRevision' = prev ∧ h.Revision' = rev⌝ ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ storeStopped s γ) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
