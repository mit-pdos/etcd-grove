/-
`checkAndGetPrevKV(trace, txnWrite, p)` (`put.go`), internal (`Put`, `checkPut`): `getPrevKV`, then
`ErrKeyNotFound` for an ignore flag on a missing key. Old spec: over the log. Round 1: 3e's API.
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
/-- `checkAndGetPrevKV(trace, rv, p)`: `ErrKeyNotFound` for an ignore flag on a key missing from the
transaction's current store; else `getPrevKV`'s result. -/
def checkAndGetPrevKV.spec : Prop :=
  ∀ (trace : Loc) (rv : GoInterface) (γ : Mvcc.MvccName) (k : Mvcc.MTxn) (p : Loc) (dq : DFrac)
    (pm : PutReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ TraceUtil.traceOwn trace ∗ Mvcc.mvccTxn rv γ trace k ∗ putReqOwn p dq pm }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.checkAndGetPrevKV)) (Val #trace)) (Val #rv)) (Val #p))
  {{ (prevKV : Loc) (err : GoInterface), RET (PairV #prevKV #err); TraceUtil.traceOwn trace ∗
      Mvcc.mvccTxn rv γ trace k ∗ putReqOwn p dq pm ∗
      (if ignores pm = true ∧ k.readHist.store pm.key = none then
         iprop(⌜prevKV = null⌝ ∗ errIs err .keyNotFound)
       else iprop(⌜err = GoInterface.nil⌝ ∗ (if needsPrev pm then
         rrOwn prevKV ((k.readHist.store pm.key).map (KV.ofRec pm.key)).toList (viewRev k)
           (k.readHist.store pm.key).toList.length
       else iprop(⌜prevKV = null⌝)))) }}

end spec
end Txn
end EtcdGrove
end Perennial
