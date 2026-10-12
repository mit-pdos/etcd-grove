/-
`applyCompares` (`txn.go`). Lean-first; see `TxnRun.lean`.
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

/-- `applyCompares(rv, cmps)` on a read transaction (of the committed log `log`): whether every
comparison holds at the state after `log` (`List.all`, the client's verdict). -/
abbrev txn.applyCompares.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (sl : GoSlice) (cps : List Loc)
    (cms : List CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ mvcc.isTxnRead mw s γ log rev ∗ sl ↦*□ cps ∗ txn.comparesIs cps cms }}
    (App (App (Val (@! txn.applyCompares))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface))) (Val #sl))
  {{ RET #(cms.all (cmpHolds (mvcc.stateAfter log))); mvcc.isTxnRead mw s γ log rev }}

end spec

end EtcdGrove
end Perennial
