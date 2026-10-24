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
it outside any lock and makes the lock, `idx_publish`), with the lock's ghost part (`idxLockG γ n`)
and the compactor's token (`idxCompactor`, no compaction yet: what `treeIndex.Compact` takes).
The caller brings the index's event count's authority at `n` (the events the rebuild will put:
`0` for `NewStore`, the restored log's for `store.Restore`) and the compactor's state, whole, both
fresh, with lower bounds of the compaction revision and the committed log (the restore plan's
R5d: `store.Restore`'s new index keeps the store's history, committed-log and compaction names).
`NewStore` takes all of fresh names (`idxFresh`, split by `idxFresh_split`; 2026-10-16, D13a: the
etcd server chooses them before `newRaftNode`). -/
abbrev mvcc.newTreeIndex.spec : Prop :=
  ∀ (γ : mvcc.IdxNames) (lg : Loc) (n : Nat) (log₀ : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ ⌜lg ≠ null⌝ ∗
      monoNatAuthOwn γ.nev 1 n ∗ ghostVar γ.cmp 1 ((-1 : Int), ([] : List Loc)) ∗
      mvcc.crevLb γ (-1) ∗ monoListLbOwn γ.log log₀ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex)) (Val #lg))
  {{ (ti : Loc), RET #(interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti);
      mvcc.ownIdxPriv ti [] ∗ mvcc.idxLockG γ n ∗ mvcc.idxCompactor γ (-1) }}

end spec

end EtcdGrove
end Perennial

