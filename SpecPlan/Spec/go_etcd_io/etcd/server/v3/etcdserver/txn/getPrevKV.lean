/-
`getPrevKV(trace, txnWrite, p)` (`put.go`), internal: with an ignore flag or `PrevKv`, the view's
`Range` of the key at revision `0` (3e's `Txn.Range`: its record in the current store; the context
`TODO()`: no error). Old spec: over the log. Round 1: 3e's API (F4).
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

/-- `getPrevKV(trace, rv, p)` on an open transaction `k`: the key's record in its current store if
the request needs it, else `nil`. -/
def getPrevKV.spec : Prop :=
  ∀ (trace : Loc) (rv : GoInterface) (γ : Mvcc.MvccName) (k : Mvcc.MTxn) (p : Loc) (dq : DFrac)
    (pm : PutReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ TraceUtil.traceOwn trace ∗ Mvcc.mvccTxn rv γ trace k ∗ putReqOwn p dq pm }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.getPrevKV)) (Val #trace)) (Val #rv)) (Val #p))
  {{ (prevKV : Loc) (err : GoInterface), RET (PairV #prevKV #err); ⌜err = GoInterface.nil⌝ ∗
      TraceUtil.traceOwn trace ∗ Mvcc.mvccTxn rv γ trace k ∗ putReqOwn p dq pm ∗
      (if needsPrev pm then
         rrOwn prevKV ((k.readHist.store pm.key).map (KV.ofRec pm.key)).toList (viewRev k)
           (k.readHist.store pm.key).toList.length
       else iprop(⌜prevKV = null⌝)) }}

end spec
end Txn
end EtcdGrove
end Perennial
