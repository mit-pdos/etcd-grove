/-
`storeTxnWrite.Changes` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

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

/-- `tw.Changes()`: the transaction's `changes`, the key-values of the pending changes
(`changesAre`), borrowed from the transaction. -/
abbrev mvcc.storeTxnWrite.Changes.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.storeTxnWriteIs tw s γ ilog pend }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Changes")) (Val #()))
  {{ (chs : GoSlice) (ps : List Loc), RET #chs;
      chs ↦* ps ∗ mvcc.changesAre ps ilog pend ∗ ⌜ps.length = pend.length⌝ ∗
      (chs ↦* ps -∗ mvcc.changesAre ps ilog pend -∗ mvcc.storeTxnWriteIs tw s γ ilog pend) }}

end spec

end EtcdGrove
end Perennial
