/-
`checkTxn(trace, rv, rt, lessor, txnPath)` (`txn.go`), internal (`Txn`, recursively): mirrors the code
(`opsCheck`: `checkRange`, `checkPut`, a nested transaction's taken branch, the first error). Old
spec: over the log.
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
/-- `checkTxn(trace, rv, rt, le, path)` at the read view `h`: `opsCheck` of the taken branch, and
the number of nested transactions on the taken path. -/
def checkTxn.spec : Prop :=
  ∀ (trace : Loc) (rv le : GoInterface) (γ : MvccName) (k : TxKind) (h : KVHist) (rt : Loc)
    (dq : DFrac) (t : TxnReq) (path : GoSlice) (rest : List Bool) (ls : Int → Option LeaseRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ traceAt trace ∗ mvccTxn rv γ k h [] ∗ txnReqOwn rt dq t ∗
      path ↦*□ (txnPathOf t h.store ++ rest) ∗
      (if t.readonly then iprop(True) else iprop(lessorAt le γ ∗ leasesPin γ ls)) }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.checkTxn)) (Val #trace)) (Val #rv)) (Val #rt)) (Val #le)) (Val #path))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); mvccTxn rv γ k h [] ∗ txnReqOwn rt dq t ∗
      (if t.readonly then iprop(True) else iprop(leasesPin γ ls)) ∗
      (match opsCheck h ls (if cmpsHold t.compare h.store then t.success else t.failure) with
       | none => iprop(⌜err = GoInterface.nil ∧ n = W64 ((txnPathOf t h.store).length - 1)⌝)
       | some e => iprop(⌜n = W64 0⌝ ∗ errIs err e)) }}

end spec
end Txn
end EtcdGrove
end Perennial
