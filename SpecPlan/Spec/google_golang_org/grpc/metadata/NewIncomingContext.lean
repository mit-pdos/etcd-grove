/-
`metadata.NewIncomingContext(ctx, md)` (grpc-go, assumed: `metadata/metadata.go`).

Users: the auth store's `WithRoot` (`auth/store.go`, 3d: the root token's context for the lessor's
revocations and the health checks).

Why true: `context.WithValue(ctx, mdIncomingKey{}, md)`: the map itself is stored (not copied), so
the caller lends it read-only for good; `FromIncomingContext` then copies it. The peer (`peerKey{}`)
is `ctx`'s: a value at another key.

Changes: new (integration I3, 3d's request).

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.metadata.Assumptions]

/-- `metadata.NewIncomingContext(ctx, md)`: a context (a child of `ctx` for cancellation and
values) whose incoming metadata is `md` and whose peer is `ctx`'s; the map lent read-only. -/
def NewIncomingContext.spec : Prop :=
  ∀ (ctx : GoInterface) (m : Loc) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ Context.ctxOk ctx ∗
      mdAt m DFrac.discard md }}
    (App (App (Val (@! google_golang_org.grpc.metadata.NewIncomingContext)) (Val #ctx)) (Val #m))
  {{ (ctx' : GoInterface), RET #ctx'; Context.ctxOk ctx' ∗ ctxInMD ctx' (some md) ∗
      □ (∀ c, ctxPeerCN ctx c -∗ ctxPeerCN ctx' c) }}

end spec

end Grpc
end EtcdGrove
end Perennial
