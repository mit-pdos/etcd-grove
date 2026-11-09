/-
`checkRange(rv, req)` (`range.go`), internal (`checkTxn`): mirrors the code against the view's `Rev()`
(the begin revision) and `FirstRev()` (the compaction revision, `-1` before any: W0's `txnRevErr`).
Old spec: same over the old model.
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

/-- `checkRange(rv, r)`: W0's `txnRevErr` at the view's history. -/
def checkRange.spec : Prop :=
  ∀ (rv : GoInterface) (γ : MvccName) (k : TxKind) (h : KVHist) (evs : List Event) (r : Loc)
    (dq : DFrac) (rm : RangeReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ mvccTxn rv γ k h evs ∗ rangeReqOwn r dq rm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.checkRange)) (Val #rv)) (Val #r))
  {{ (err : GoInterface), RET #err; mvccTxn rv γ k h evs ∗ rangeReqOwn r dq rm ∗
      (match rm.txnRevErr h with
       | none => iprop(⌜err = GoInterface.nil⌝)
       | some e => errIs err e) }}

end spec
end Txn
end EtcdGrove
end Perennial
