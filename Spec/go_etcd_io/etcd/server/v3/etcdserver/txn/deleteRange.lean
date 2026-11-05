/-
`txn.deleteRange` (delete.go). Lean-first (no Rocq counterpart); see `Proof/.../etcdserver/txn/Write.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccReachable MvccName MvccStorage mvccN mvccLeases)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

/-- `deleteRange(ctx, txnWrite, dr)` at a write transaction begun at `σ` with `pend` pending.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.deleteRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (tw : GoInterface)
    (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (pend : List mvcc.Change) (dr : Loc)
    (o : OpFull) (L : List w64),
  {{ pkgInit ∗ mvcc.txnCtx ctx cd ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      mvcc.api.mvccTxn tw γ trace (.write σ pend) ∗ traceutil.ownTrace trace te ∗
      ⌜txn.Reach σ⌝ ∗ txn.deleteRangeRequestIs dr o ∗
      lease.leaseOwn (mvccLeases γ) L (mvcc.pendItems σ.log pend) }}
    (App (App (App (Val (@! txn.deleteRange)) (Val #(GoInterface.ok ctx))) (Val #tw)) (Val #dr))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); traceutil.ownTrace trace te ∗
      ((⌜err = GoInterface.nil⌝ ∗
        mvcc.api.mvccTxn tw γ trace (.write σ (pend ++ txn.delChanges (txn.pendState σ.log pend) o)) ∗
        txn.deleteRangeResponseIs resp
          (W64 ((mvcc.writeRev σ.log (pend ++ txn.delChanges (txn.pendState σ.log pend) o) : Nat) :
            Int))
          (rangeIn (txn.pendState σ.log pend) o).length
          (if o.base.prevKV then rangeIn (txn.pendState σ.log pend) o else []) ∗
        txn.respHdrOwn (structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
        lease.leaseOwn (mvccLeases γ) L
          (mvcc.pendItems σ.log (pend ++ txn.delChanges (txn.pendState σ.log pend) o))) ∨
      (⌜err ≠ GoInterface.nil ∧ o.base.prevKV = true ∧ resp = null ∧ nd = false⌝ ∗
        mvcc.api.mvccTxn tw γ trace (.write σ pend) ∗
        lease.leaseOwn (mvccLeases γ) L (mvcc.pendItems σ.log pend))) }}

end spec

end EtcdGrove
end Perennial
