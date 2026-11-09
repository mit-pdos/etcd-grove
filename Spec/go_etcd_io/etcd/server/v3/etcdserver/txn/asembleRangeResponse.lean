/-
`asembleRangeResponse(rr, r)` (`range.go`), internal: mirrors the code (`assemble`; the result's key-
values move into the reply, a keys-only one's values set to `nil`). Old spec: same over the old model.
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

/-- `asembleRangeResponse(rr, r)`: the reply at `rr`'s revision, its key-values and `More` by
`assemble`, `Count` `rr`'s. -/
def asembleRangeResponse.spec : Prop :=
  ∀ (rr r : Loc) (dq : DFrac) (rm : RangeReq) (kvs : List KV) (rev c : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ rrOwn rr kvs rev c ∗ rangeReqOwn r dq rm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.asembleRangeResponse)) (Val #rr)) (Val #r))
  {{ (resp : Loc), RET #resp; rangeReqOwn r dq rm ∗
      rangeOk resp rev { kvs := (assemble rm kvs).1, more := (assemble rm kvs).2, count := c } }}

end spec
end Txn
end EtcdGrove
end Perennial
