/-
## `IsDefaultOrdering(sortTarget, sortOrder)` (`range.go`)

**Users.** The gRPC layer's `checkRangeRequest` (`api/v3rpc/key.go:173`), `rangeLimit`,
`sortRangeResults`. Snippet: `examples/specreq/txn/helpers.go` (`ReqSortHelpers`).

**Proof sketch.** The expression.

**Changes.** Unchanged (W0's `isDefaultOrdering`). **Margin.** None.
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

open Classical in
/-- `IsDefaultOrdering(target, order)`: no order, or ascending by key (W0's `isDefaultOrdering`). -/
def IsDefaultOrdering.spec : Prop :=
  ∀ (tg od : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.IsDefaultOrdering)) (Val #tg)) (Val #od))
  {{ RET #(decide (isDefaultOrdering (sint.Z tg) (sint.Z od))); True }}

end spec
end Txn
end EtcdGrove
end Perennial
