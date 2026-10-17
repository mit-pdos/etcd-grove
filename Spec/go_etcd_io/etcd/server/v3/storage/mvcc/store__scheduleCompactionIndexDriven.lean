/-
`store.scheduleCompactionIndexDriven` (`kvstore_compaction.go`, etcd-io/etcd#21951): the index-driven compaction job's pass.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

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

/-- `s.scheduleCompactionIndexDriven(rev, prev)` (etcd-io/etcd#21951, the `IndexDrivenCompaction`
feature gate's compaction; `compactJobPre`), with the index compactor's token at or below `rev`
(`compactTok`): the index compacted at `rev` (`treeIndex.Compact`: the map of the revisions it
drops, `delSetOk`; the token at `rev` after it, whatever follows), then those revisions' bucket
keys deleted, sorted, in batches of `CompactionBatchLimit` (positive: `isStore`) under the batch
lock (`UnsafeDelete` of keys compaction may delete, `delKey`), each committed,
`finishedCompactRev = rev` written in the last batch: `nil` and the compaction finished
(`compactedAt γ rev`); or the store stopped between two batches (its stop channel closed):
`fmt.Errorf`'s error. The same as `scheduleCompaction`'s, but no hash: the zero `KeyValueHash`. -/
abbrev mvcc.store.scheduleCompactionIndexDriven.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev prev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.compactJobPre s γ rev ∗
      mvcc.compactTok γ (sint.Z rev) }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"scheduleCompactionIndexDriven"))
      (Val #rev)) (Val #prev))
  {{ (err : GoInterface), RET (PairV #(zero_val KeyValueHash) #err);
      mvcc.idxCompactor γ.idx (sint.Z rev) ∗
      ((⌜err = GoInterface.nil⌝ ∗ mvcc.compactedAt γ (sint.Z rev)) ∨
        (mvcc.errorfIs err ∗ mvcc.storeStopped s)) }}

end spec

end EtcdGrove
end Perennial
