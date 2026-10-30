/-
`withVersion(ctx)` (`client/v3/ctx.go`, names only; unit P3a): the context with the client's API
version in its outgoing gRPC metadata (`metadata.FromOutgoingContext`, `Pairs`, `MD.Copy`,
`MD.Set`, `NewOutgoingContext`: grpc's `metadata`, names only).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry
public import Proof.google_golang_org.grpc.metadata.Outgoing

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `withVersion(ctx)` returns a context derived from `ctx` by a value (grpc's
`NewOutgoingContext` is `context.WithValue`): the same `Done` and `Err` (`isContext` with `ctx`'s
descriptor, its values changed; since the vertical slice's unit V2 for any `ctxOk` context: a quiet
one, `context.TODO()`, gives a quiet one, `valueCtx` delegating `Err` to its parent). Since
2026-10-28 (the auth plan's E3zc) with its outgoing metadata: `ctx`'s, the API version's key
(`rpctypes.MetadataClientAPIVersionKey`, `client-api-version`) set to one value (`version.APIVersion`,
computed at the package's initialization), every other key as in `ctx` (`metadata.mdSet`: `Pairs`
when `ctx` has none, else `MD.Copy` and `MD.Set`; `FromOutgoingContext` reads what
`metadata.outgoingOf` models). -/
abbrev withVersion.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ctxOk ctx cd }}
    (App (Val (@! go_etcd_io.etcd.client.v3.withVersion)) (Val #(GoInterface.ok ctx)))
  {{ (c' : GoInterface), RET #c'; ∃ (ci : GoInterfaceOk) (vs : GMap GoInterface GoInterface),
      ⌜c' = GoInterface.ok ci⌝ ∗ ctxOk ci { cd with Values := vs } ∗
      ⌜∃ v : GoString, metadata.outgoingOf c' =
        metadata.mdSet (metadata.outgoingOf (GoInterface.ok ctx)) go!"client-api-version" [v]⌝ }}

end spec

end EtcdGrove
end Perennial
