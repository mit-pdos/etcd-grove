/-
`newTreeIndex` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
-/
module

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
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newTreeIndex(lg)` (a non-nil logger): a fresh tree index (as the `index` interface), private
(`ownIdxPriv`: its `RWMutex` not yet a lock, the restore plan's R3 design point: `restore` rebuilds
it outside any lock and makes the lock, `idx_publish`), with the lock's ghost part
(`idxLockG`, no event yet), its writer's handle for the empty log, the other half of the committed
log's authority (`idxLogAuth`), the whole authority of the compaction revision at `-1` (none;
`crevUB`, which the store splits between its locks and the compaction right) and the compactor's
token (`idxCompactor`, no compaction yet: what `treeIndex.Compact` takes). The
index's ghost names `γ` are the caller's, fresh (`mvcc.idxFresh`, `mvcc.idxFresh_alloc`;
2026-10-16, D13a: the etcd server chooses them before `newRaftNode`). -/
abbrev mvcc.newTreeIndex.spec : Prop :=
  ∀ (γ : mvcc.IdxNames) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ ⌜lg ≠ null⌝ ∗
      mvcc.idxFresh γ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex)) (Val #lg))
  {{ (ti : Loc), RET #(interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti);
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockG γ 0 ∗ mvcc.idxWriter γ [] [] ∗
        mvcc.idxLogAuth γ (1 : Qp).half [] ∗ mvcc.crevUB γ 1 (-1) ∗ mvcc.idxCompactor γ (-1) }}

end spec

end EtcdGrove
end Perennial

