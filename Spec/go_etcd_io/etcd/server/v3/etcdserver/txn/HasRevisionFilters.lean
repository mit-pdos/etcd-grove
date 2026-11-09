/-
## `HasRevisionFilters(r)` (`range.go`)

**Users.** The gRPC layer's `checkRangeRequest` (`api/v3rpc/key.go:176`), `rangeLimit`. Snippet:
`examples/specreq/txn/helpers.go` (`ReqSortHelpers`).

**Proof sketch.** Four field reads (`rangeReqOwn`'s unfold law). **Changes.** Unchanged (W0's
`hasRevFilters`). **Margin.** None.
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
/-- `HasRevisionFilters(r)`: some revision filter is set (W0's `RangeReq.hasRevFilters`). -/
def HasRevisionFilters.spec : Prop :=
  ∀ (r : Loc) (dq : DFrac) (rm : RangeReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ rangeReqOwn r dq rm }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.HasRevisionFilters)) (Val #r))
  {{ RET #(decide rm.hasRevFilters); rangeReqOwn r dq rm }}

end spec
end Txn
end EtcdGrove
end Perennial
