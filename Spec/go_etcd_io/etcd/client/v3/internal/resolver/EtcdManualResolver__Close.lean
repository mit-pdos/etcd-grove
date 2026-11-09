/-
`(*resolver.EtcdManualResolver).Close` (`client/v3/internal/resolver/resolver.go`; promoted from
grpc's `manual.Resolver`).

Users: `newClient`'s dial error path.

Proof sketch: grpc's `manual.Resolver.Close` (2a).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/internal/resolver/EtcdManualResolver__Close.lean`.

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

/-- `r.Close()`: the resolver consumed. -/
def EtcdManualResolver.Close.spec : Prop :=
  ∀ (r : Loc) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver ∗ resolverAt r eps }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty @!! go!"Close")) (Val #()))
  {{ RET #(); True }}

end spec

end Resolver
end EtcdGrove
end Perennial
