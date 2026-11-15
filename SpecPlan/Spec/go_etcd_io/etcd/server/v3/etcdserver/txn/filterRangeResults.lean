/-
`filterRangeResults(rr, r)` (`range.go`), internal: mirrors the code (four `pruneKVs` with closures
over the request's fields; W0's `RangeReq.keeps`). Old spec: same over the old model.
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

/-- `filterRangeResults(rr, r)`: keeps the key-values the revision filters keep, in order. -/
def filterRangeResults.spec : Prop :=
  ∀ (rr r : Loc) (dq : DFrac) (rm : RangeReq) (kvs : List KV) (rev c : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ rrOwn rr kvs rev c ∗ rangeReqOwn r dq rm }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.filterRangeResults)) (Val #rr)) (Val #r))
  {{ RET #(); rrOwn rr (kvs.filter rm.keeps) rev c ∗ rangeReqOwn r dq rm }}

end spec
end Txn
end EtcdGrove
end Perennial
