/-
`store.scheduleCompaction` (`kvstore_compaction.go`): the compaction job's pass (2026-10-13, unit 5a).
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

/-- `s.scheduleCompaction(rev, prev)` (`compactJobPre`), with the index compactor's token at or
below `rev` (`compactTok`: the job's, handed on by the previous job; 2026-10-13, unit 5c): the
index compacted at `rev` (`treeIndex.Compact`: the map of the kept revisions; the token at `rev`
after it, whatever follows), then the bucket's revisions up to `rev` not kept deleted in batches
of `CompactionBatchLimit` (positive: `isStore`) under the batch lock (`UnsafeRange` limited,
`UnsafeDelete` of keys compaction may delete, `delKey`), each committed, `finishedCompactRev = rev`
written in the last batch: `nil` and the compaction finished (`compactedAt γ rev`); or the store
stopped between two batches (its stop channel closed): `fmt.Errorf`'s error. The hash
(`kvHasher`, crc32: an axiom) is any. -/
abbrev mvcc.store.scheduleCompaction.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev prev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.compactJobPre s γ rev ∗
      mvcc.compactTok γ (sint.Z rev) }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"scheduleCompaction")) (Val #rev))
      (Val #prev))
  {{ (h : KeyValueHash) (err : GoInterface), RET (PairV #h #err);
      mvcc.idxCompactor γ.idx (sint.Z rev) ∗
      ((⌜err = GoInterface.nil⌝ ∗ mvcc.compactedAt γ (sint.Z rev)) ∨
        (mvcc.errorfIs err ∗ mvcc.storeStopped s)) }}

end spec

end EtcdGrove
end Perennial
