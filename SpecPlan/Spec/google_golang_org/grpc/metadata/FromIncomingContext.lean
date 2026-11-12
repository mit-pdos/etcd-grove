/-
`metadata.FromIncomingContext(ctx)` (grpc-go, assumed: `metadata/metadata.go`).

Users: `v3rpc.newUnaryInterceptor`, `newStreamInterceptor` (`interceptor.go:58,212`, this batch,
on a run's context: `rpcCtx_inMD`); the auth store's `AuthInfoFromCtx`/`AuthInfoFromTLS` (3d, on any
context: the server's `s.ctx` and its children have none).

Why true: the run's context carries the incoming metadata grpc decoded from the headers
(`rpcCtx`); `FromIncomingContext` returns a fresh copy with lowercased keys and `true` (every run's
context has one).

Changes: new. Integration I3 (3d's request): stated for any context over `ctxInMD` (was a run's
context only, `rpcCtx`; `rpcCtx_inMD` gives it).

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

/-- `metadata.FromIncomingContext(ctx)`: a fresh copy of the context's incoming metadata and
`true`, or `nil` and `false` for a context with none. -/
def FromIncomingContext.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ ctxInMD ctx o }}
    (App (Val (@! google_golang_org.grpc.metadata.FromIncomingContext)) (Val #ctx))
  {{ (m : Loc) (ok : Bool), RET (PairV #m #ok);
      match o with
      | some md => ⌜ok = true⌝ ∗ mdAt m (DFrac.own 1) md
      | none => ⌜ok = false ∧ m = null⌝ }}

end spec

end Grpc
end EtcdGrove
end Perennial
