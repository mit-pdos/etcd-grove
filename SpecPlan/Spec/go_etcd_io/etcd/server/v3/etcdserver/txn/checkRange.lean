/-
`checkRange(rv, req)` (`range.go`), internal (`checkTxn`): mirrors the code against the read
transaction's `Rev()` and `FirstRev()` (3e: `σ.rev`, `σ.crev`, `-1` before any compaction: W0's
`txnRevErr`). Only a read transaction, the one Go passes (`txn.go:54`): a write transaction's
`FirstRev()` is `0` (round 1, F3). Old spec: same over the old model.
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

/-- `checkRange(rv, r)` at a read transaction at `σ`: W0's `txnRevErr` at `σ.kv`. -/
def checkRange.spec : Prop :=
  ∀ (rv : GoInterface) (γ : Mvcc.MvccName) (tr : Loc) (σ : Mvcc.MvccState) (r : Loc) (dq : DFrac)
    (rm : RangeReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Mvcc.mvccTxn rv γ tr (.read σ) ∗ rangeReqOwn r dq rm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.checkRange)) (Val #rv)) (Val #r))
  {{ (err : GoInterface), RET #err; Mvcc.mvccTxn rv γ tr (.read σ) ∗ rangeReqOwn r dq rm ∗
      (match rm.txnRevErr σ.kv with
       | none => iprop(⌜err = GoInterface.nil⌝)
       | some e => errIs err e) }}

end spec
end Txn
end EtcdGrove
end Perennial
