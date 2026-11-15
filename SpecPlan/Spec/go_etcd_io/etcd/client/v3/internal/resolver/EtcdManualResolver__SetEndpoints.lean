/-
`(*resolver.EtcdManualResolver).SetEndpoints` (`client/v3/internal/resolver/resolver.go`).

Users: `Client.SetEndpoints` (under `epMu`).

Proof sketch: stores the slice; `updateState`: `getCC` (grpc's `CC()`, its panic before `Build`
recovered), then `UpdateState(r.state())` (`endpoint.Interpret` per endpoint; grpc, 2a).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/internal/resolver/EtcdManualResolver__SetEndpoints.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.internal.resolver.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Resolver

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.internal.resolver.Assumptions]

/-- `r.SetEndpoints(eps)`: the resolver's endpoints replaced. -/
def EtcdManualResolver.SetEndpoints.spec : Prop :=
  ∀ (r : Loc) (eps : List GoString) (sl : GoSlice) (eps' : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver ∗ resolverAt r eps ∗ sl ↦*□ eps' }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty @!! go!"SetEndpoints")) (Val #sl))
  {{ RET #(); resolverAt r eps' }}

end spec

end Resolver
end EtcdGrove
end Perennial
