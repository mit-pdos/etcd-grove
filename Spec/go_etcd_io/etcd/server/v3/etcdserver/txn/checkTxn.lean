/-
`checkTxn(trace, rv, rt, lessor, txnPath)` (`txn.go`), internal (`Txn`, recursively): mirrors the code
(`opsCheck`: `checkRange`, `checkPut`, a nested transaction's taken branch, the first error). Only at
a read transaction, the one Go passes (round 1, F3). Old spec: over the log.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

open Classical in
/-- `checkTxn(trace, rv, rt, le, path)` at a read transaction at `σ`: `opsCheck` of the taken branch,
and the number of nested transactions on the taken path. -/
def checkTxn.spec : Prop :=
  ∀ (trace : Loc) (rv le : GoInterface) (γ : Mvcc.MvccName) (σ : Mvcc.MvccState) (rt : Loc)
    (dq : DFrac) (t : TxnReq) (path : GoSlice) (rest : List Bool) (leL : Loc) (γl : Lease.Names)
    (c : Lease.Cfg) (n : Nat) (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ TraceUtil.traceOwn trace ∗ Mvcc.mvccTxn rv γ trace (.read σ) ∗ txnReqOwn rt dq t ∗
      path ↦*□ (txnPathOf t σ.kv.store ++ rest) ∗
      (if t.readonly then iprop(True)
       else iprop(⌜le = Lease.lessorIface leL⌝ ∗ Lease.isLessor leL γl c ∗ Lease.lessorState γl n ls)) }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.checkTxn)) (Val #trace)) (Val #rv)) (Val #rt)) (Val #le)) (Val #path))
  {{ (cnt : w64) (err : GoInterface), RET (PairV #cnt #err); TraceUtil.traceOwn trace ∗
      Mvcc.mvccTxn rv γ trace (.read σ) ∗ txnReqOwn rt dq t ∗
      (if t.readonly then iprop(True) else iprop(Lease.lessorState γl n ls)) ∗
      (match opsCheck σ.kv ls.table (if cmpsHold t.compare σ.kv.store then t.success else t.failure) with
       | none => iprop(⌜err = GoInterface.nil ∧ cnt = W64 ((txnPathOf t σ.kv.store).length - 1)⌝)
       | some e => iprop(⌜cnt = W64 0⌝ ∗ errIs err e)) }}

end spec
end Txn
end EtcdGrove
end Perennial
