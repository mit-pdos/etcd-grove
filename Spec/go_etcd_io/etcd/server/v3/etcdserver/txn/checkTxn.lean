/-
`checkTxn` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`.
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
open mvcc.api (MvccState MTxn MvccReachable MvccName BkRef mvccN mvccLeases)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

/-- `checkTxn(trace, rv, rt, lessor, txnPath)` on a read transaction at `σ`: the checks of the
path's ranges and puts (`checkRange`, `checkPut`), the number of nested transactions, or the first
error.

(Strict M1, 2026-11-05: over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean` drafts it.)
(The trace kept at `te`: `Trace.StepWithFunction` keeps the flag, decided by the coordinator,
2026-11-05, superseding gap E.) -/

abbrev txn.checkTxn.spec : Prop :=
  ∀ (tw : GoInterface) (γ : MvccName) (trace : Loc) (te : Bool) (σ : MvccState) (rt : Loc)
    (t : TxnModel) (le : GoInterface) (γl : GName) (pl : GoSlice) (rest : List Bool)
    (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (lu : Bool),
  (lu = false → txn.txnReadonly t = true) →
  {{ pkgInit ∗ ⌜trace ≠ null⌝ ∗ mvcc.api.mvccTxn tw γ trace (.read σ) ∗
      traceutil.ownTrace trace te ∗ ⌜txn.Reach σ⌝ ∗ txn.txnRequestIs rt t ∗
      txn.isTxnLessor le γl ∗ (⌜lu = false⌝ ∨ lease.lessorUser γl L I) ∗
      pl ↦*□ (txn.txnPath (mvcc.stateAfter σ.log) t ++ rest) }}
    (App (App (App (App (App (Val (@! txn.checkTxn)) (Val #trace)) (Val #tw)) (Val #rt)) (Val #le))
      (Val #pl))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); mvcc.api.mvccTxn tw γ trace (.read σ) ∗
      traceutil.ownTrace trace te ∗ (⌜lu = false⌝ ∨ lease.lessorUser γl L I) ∗
      ((⌜err = GoInterface.nil ∧ n = W64 (txn.nestedCount (mvcc.stateAfter σ.log) t : Int) ∧
          txn.PathsIgnOk (mvcc.stateAfter σ.log)
            (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t))⌝ ∗
        txn.leasesOk L (txn.opsLeases (mvcc.stateAfter σ.log)
          (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t)))) ∨
       (⌜err ≠ GoInterface.nil ∧ n = W64 0 ∧
          (txn.txnLeased t → ¬ (txn.PathsIgnOk (mvcc.stateAfter σ.log)
            (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t)) ∧ txn.PathsLeaseOk (mvcc.stateAfter σ.log) L
            (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t))))⌝ ∗ txn.checkErrIs err)) }}

end spec

end EtcdGrove
end Perennial
