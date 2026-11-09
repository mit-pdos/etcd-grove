/-
`metadata.NewOutgoingContext(ctx, md)` (grpc-go, assumed: `metadata/metadata.go`).

Users: the client's `WithRequireLeader`, `withVersion` (W0, 1c), `examples/etcd/auth/authkv.go`.

Why true: it returns `context.WithValue(ctx, mdOutgoingKey{}, rawMD{md: md})`, keeping the map (not
copied: the caller must not write it afterwards, hence the read-only `mdAt`).

Changes: from `specs-ref/Spec/google_golang_org/grpc/metadata/NewOutgoingContext.lean` (if any:
the old `AppendToOutgoingContext` was its only neighbor).

Margin: none.
-/
module

public import Spec.google_golang_org.grpc.Api

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

/-- `metadata.NewOutgoingContext(ctx, md)` with a read-only map: a context carrying `md` as its
outgoing metadata, `ctx`'s values otherwise. -/
def NewOutgoingContext.spec : Prop :=
  ∀ (ctx : GoInterface) (m : Loc) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ Context.ctxOk ctx ∗ mdAt m DFrac.discard md }}
    (App (App (Val (@! google_golang_org.grpc.metadata.NewOutgoingContext)) (Val #ctx)) (Val #m))
  {{ (ctx' : GoInterface), RET #ctx'; Context.ctxOk ctx' ∗ Context.ctxWithValues ctx ctx' ∗
      outMD ctx' md }}

end spec

end Grpc
end EtcdGrove
end Perennial
