/-
`resolver.New` (`client/v3/internal/resolver/resolver.go`).

Users: `newClient` (the client's resolver), `Client.Dial` (one endpoint's).

Proof sketch: `manual.NewBuilderWithScheme` (grpc, 2a), the struct allocated with the caller's
slice (kept: read-only).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/internal/resolver/New.lean`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.Api

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

/-- `New(eps...)`: a resolver with the endpoints. -/
def New.spec : Prop :=
  ∀ (sl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver ∗ sl ↦*□ eps }}
    (App (Val (@! go_etcd_io.etcd.client.v3.internal.resolver.New)) (Val #sl))
  {{ (r : Loc), RET #r; resolverAt r eps }}

end spec

end Resolver
end EtcdGrove
end Perennial
