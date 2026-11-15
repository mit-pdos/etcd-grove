/-
`rangeLimit(r)` (`range.go`), internal (`executeRange`): mirrors the code (`rangeLimitZ`; W0's
`pushdownLimit` up to `MaxInt64`). Old spec: same (over the old request model).
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

/-- `rangeLimit(r)`: `rangeLimitZ`. -/
def rangeLimit.spec : Prop :=
  ∀ (r : Loc) (dq : DFrac) (rm : RangeReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ rangeReqOwn r dq rm }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.rangeLimit)) (Val #r))
  {{ RET #(W64 (rangeLimitZ rm)); rangeReqOwn r dq rm }}

end spec
end Txn
end EtcdGrove
end Perennial
