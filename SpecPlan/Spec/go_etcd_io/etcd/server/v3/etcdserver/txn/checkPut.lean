/-
`checkPut(trace, rv, lessor, p)` (`put.go`), internal (`checkTxn`): `checkLease`, then
`checkAndGetPrevKV` (its error only); W0's `PutReq.check` at the view's current store. Old spec:
over the log. Round 1: 3e's API (F4).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

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

/-- `checkPut(trace, rv, le, p)` on an open transaction `k`: W0's `PutReq.check` at its current store
and the writer's live leases. -/
def checkPut.spec : Prop :=
  ∀ (trace : Loc) (rv : GoInterface) (γ : Mvcc.MvccName) (k : Mvcc.MTxn) (p : Loc) (dq : DFrac)
    (pm : PutReq) (leL : Loc) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat) (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ TraceUtil.traceOwn trace ∗ Mvcc.mvccTxn rv γ trace k ∗ Lease.isLessor leL γl c ∗
      Lease.lessorState γl n ls ∗ putReqOwn p dq pm }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.checkPut)) (Val #trace)) (Val #rv)) (Val #(Lease.lessorIface leL))) (Val #p))
  {{ (err : GoInterface), RET #err; TraceUtil.traceOwn trace ∗ Mvcc.mvccTxn rv γ trace k ∗
      Lease.lessorState γl n ls ∗ putReqOwn p dq pm ∗
      (match pm.check k.readHist.store ls.table with
       | none => iprop(⌜err = GoInterface.nil⌝)
       | some e => errIs err e) }}

end spec
end Txn
end EtcdGrove
end Perennial
