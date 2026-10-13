/-
`txn.deleteRange` (delete.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `deleteRange(ctx, txnWrite, dr)` at a write transaction (committed log `ilog`, pending
changes `pend`): the keys of the request's range at the state read deleted (`delChanges`: the
client's filter), the response with their number, the transaction's revision after the deletes
and (`PrevKv`) the deleted key-values, read-only; or, with `PrevKv`, the range read's context error
(`ctx` done; not at a context never canceled, `nd`), nothing deleted. -/
abbrev txn.deleteRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (mw s : Loc)
    (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change) (puts deletes putSize : w64)
    (dr : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ mvcc.txnCtx ctx cd ∗
      (if nd then mvcc.neverDone cd else iprop(True)) ∗
      mvcc.isTxnWrite mw s γ ilog pend puts deletes putSize ∗ txn.deleteRangeRequestIs dr o ∗
      ⌜pend.length + (rangeIn (txn.pendState ilog pend) o).length < 2 ^ 63⌝ }}
    (App (App (App (Val (@! txn.deleteRange)) (Val #(GoInterface.ok ctx))) (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface))) (Val #dr))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗
        (∃ deletes' : w64, mvcc.isTxnWrite mw s γ ilog
          (pend ++ txn.delChanges (txn.pendState ilog pend) o) puts deletes' putSize) ∗
        txn.deleteRangeResponseIs resp
          (W64 ((mvcc.writeRev ilog (pend ++ txn.delChanges (txn.pendState ilog pend) o) : Nat) :
            Int))
          (rangeIn (txn.pendState ilog pend) o).length
          (if o.base.prevKV then rangeIn (txn.pendState ilog pend) o else []) ∗
        txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse go!"Header" resp)) ∨
      (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
        mvcc.isTxnWrite mw s γ ilog pend puts deletes putSize) }}

end spec

end EtcdGrove
end Perennial
