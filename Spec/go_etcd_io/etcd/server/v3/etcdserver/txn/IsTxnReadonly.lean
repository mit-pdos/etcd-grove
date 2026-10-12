/-
`IsTxnReadonly` (`txn.go`). Lean-first; see `TxnRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `IsTxnReadonly(r)`: every operation of both branches is a range (`txnReadonly`). -/
abbrev txn.IsTxnReadonly.spec : Prop :=
  ∀ (rt : Loc) (t : TxnModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.txnRequestIs rt t }}
    (App (Val (@! txn.IsTxnReadonly)) (Val #rt))
  {{ RET #(txn.txnReadonly t); True }}

end spec

end EtcdGrove
end Perennial
