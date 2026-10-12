/-
`applyCompare` (`txn.go`). Lean-first; see `TxnRun.lean`.
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

/-- `applyCompare(rv, c)` on a read transaction (of the committed log `log`): the client model's
`cmpHolds` of the comparison at the state after `log` (the range read at `context.TODO()`, which
does not fail). -/
abbrev txn.applyCompare.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (c : Loc) (cm : CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ mvcc.isTxnRead mw s γ log rev ∗ txn.compareIs c cm }}
    (App (App (Val (@! txn.applyCompare))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface))) (Val #c))
  {{ RET #(cmpHolds (mvcc.stateAfter log) cm); mvcc.isTxnRead mw s γ log rev }}

end spec

end EtcdGrove
end Perennial
