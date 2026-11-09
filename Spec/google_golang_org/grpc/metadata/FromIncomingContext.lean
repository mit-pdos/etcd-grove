/-
`metadata.FromIncomingContext(ctx)` (grpc-go, assumed: `metadata/metadata.go`).

Users: `v3rpc.newUnaryInterceptor`, `newStreamInterceptor` (`interceptor.go:58,212`, this batch);
the server's `AuthInfoFromCtx` (2c: the `token` key).

Why true: the run's context carries the incoming metadata grpc decoded from the headers
(`rpcCtx`); `FromIncomingContext` returns a fresh copy with lowercased keys and `true` (every run's
context has one).

Changes: new.

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

/-- `metadata.FromIncomingContext(ctx)` of a run's context: a fresh copy of its metadata, `true`. -/
def FromIncomingContext.spec : Prop :=
  ∀ (ctx : GoInterface) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ rpcCtx ctx md }}
    (App (Val (@! google_golang_org.grpc.metadata.FromIncomingContext)) (Val #ctx))
  {{ (m : Loc) (ok : Bool), RET (PairV #m #ok); ⌜ok = true⌝ ∗ mdAt m (DFrac.own 1) md }}

end spec

end Grpc
end EtcdGrove
end Perennial
