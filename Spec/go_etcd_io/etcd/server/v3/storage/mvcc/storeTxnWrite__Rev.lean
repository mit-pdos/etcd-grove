/-
`storeTxnWrite.Rev` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `tw.Rev()`: the committed log's last revision (`beginRev`). -/
abbrev mvcc.storeTxnWrite.Rev.spec : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.storeTxnWriteIs tw s γ ilog pend }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #(W64 ((ilog.length : Int) - 1) : w64); mvcc.storeTxnWriteIs tw s γ ilog pend }}

end spec

end EtcdGrove
end Perennial
