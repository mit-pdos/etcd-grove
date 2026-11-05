/-
`executeRange` (`range.go`): a range on a transaction (`Range`'s read transaction, `Txn`'s write
transaction or read-only wrapper). Lean-first; see `InvRange.lean`, `RangeModel.lean`,
`InvTxn.lean`.
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

/-- `executeRange(ctx, lg, txnRead, r, withTotalCount)` at a transaction of either kind:
`rangeResult` at the log and revision it reads. No sort premise: the sort's (`sortSmall`) comes
from its `Txn.Range` call's `stateOk` at the revision read (`srvPre_stateOk`, below).

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.executeRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (tw : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (k : MTxn) (r : Loc) (o : OpFull)
    (withTotal : Bool),
  {{ pkgInit ∗ mvcc.api.mvccTxn tw γ trace k ∗ traceutil.ownTrace trace te ∗ mvcc.txnCtx ctx cd ∗
      (if nd then mvcc.neverDone cd else iprop(True)) ∗ traceutil.ctxTraceIs ctx (some trace) ∗
      txn.rangeRequestIs r o ∗
      ⌜txn.Reach k.state ∧ txn.validSortTarget o⌝ }}
    (App (App (App (App (App (Val (@! txn.executeRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #tw)) (Val #r)) (Val #withTotal))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      mvcc.api.mvccTxn tw γ trace k ∗ traceutil.ownTrace trace te ∗
      txn.rangeResult resp err k.readLog k.readRev k.state.crev o withTotal ∗ txn.rangeHdr resp err ∗
      ⌜nd = true → err = GoInterface.nil ∨ sint.Z k.readRev < sint.Z o.base.rev ∨
        sint.Z (mvcc.rangeRev k.readRev o.base.rev) < k.state.crev⌝ }}

end spec

end EtcdGrove
end Perennial
