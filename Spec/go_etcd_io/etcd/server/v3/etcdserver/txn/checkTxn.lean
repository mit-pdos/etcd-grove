/-
`checkTxn` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`.
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

/-- `checkTxn(trace, rv, rt, lessor, txnPath)` on a read transaction (of the committed log `log`),
the path `txnPath` of `rt` at the state after `log` (and anything after it): the checks of the
chosen branch's ranges (`checkRange`) and puts (`checkPut`), nested transactions by their
verdicts. Either `nil`, the number of nested transactions, every put that needs the previous
key-value finding it (`PathsIgnOk`) and every lease the puts name known (`leasesOk`); or one of
the checks' errors (`checkErrIs`) and `0` (a nested call's count is used before its error is
tested). Nothing is written. -/
abbrev txn.checkTxn.spec : Prop :=
  ∀ (trace mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (rt : Loc)
    (t : TxnModel) (le : GoInterface) (γl : GName) (pl : GoSlice) (rest : List Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ ⌜trace ≠ null⌝ ∗ mvcc.isTxnRead mw s γ log rev ∗ txn.txnRequestIs rt t ∗
      txn.isTxnLessor le γl ∗ pl ↦*□ (txn.txnPath (mvcc.stateAfter log) t ++ rest) }}
    (App (App (App (App (App (Val (@! txn.checkTxn)) (Val #trace))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface)))
      (Val #rt)) (Val #le)) (Val #pl))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); mvcc.isTxnRead mw s γ log rev ∗
      ((⌜err = GoInterface.nil ∧ n = W64 (txn.nestedCount (mvcc.stateAfter log) t : Int) ∧
          txn.PathsIgnOk (mvcc.stateAfter log)
            (t.branch (txn.txnOk (mvcc.stateAfter log) t))⌝ ∗
        txn.leasesOk γl (txn.opsLeases (mvcc.stateAfter log)
          (t.branch (txn.txnOk (mvcc.stateAfter log) t)))) ∨
       (⌜err ≠ GoInterface.nil ∧ n = W64 0⌝ ∗ txn.checkErrIs err)) }}

end spec

end EtcdGrove
end Perennial
