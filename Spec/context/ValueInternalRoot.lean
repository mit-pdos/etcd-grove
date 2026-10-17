/-
A context's `Value` at the auth store's `internalRootContextKey{}` (etcd-io/etcd#22493,
`pr-verify/etcd-22493`: `authStore.AuthInfoFromCtx` looks it up first): the trust boundary.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.RootCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Every context carries some root value** (`auth.ctxRootIs`): its
`Value(internalRootContextKey{})` returns, without effect, the same value from every call and
goroutine (Go's contract of `Context.Value`: "Successive calls to Value with the same key
returns the same result"; Perennial's `isContext` specifies `Value` only at `&cancelCtxKey`,
and `AuthInfoFromCtx` takes any context, as grpc's `FromIncomingContext` does at its trust
boundary). A value of type `internalRootContextValue` is `some x`, anything else `none`.
It is stated of every interface value, which is broader than true: a typed-nil context
(`(*myCtx)(nil)`), a value with no `Value` method, or a custom `Context` with a stateful `Value`
breaks it. It holds of the contexts the server's requests carry: chains of the standard
library's `valueCtx`/`cancelCtx`/`timerCtx` over `Background()`/`TODO()` (grpc's metadata, otel's
spans and etcd's trace values are `WithValue`s; etcd defines no `Value` of its own), whose
`Value` compares keys by dynamic type first and never panics. Base `AuthInfoFromCtx` already
called `ctx.Value` (in grpc's `FromIncomingContext`, at the trust boundary) on any context. -/
abbrev context.ValueInternalRoot.spec : Prop :=
  ∀ (ctx : GoInterfaceOk), ⊢ (iprop(∃ o, auth.ctxRootIs (GF := GF) ctx o) : IProp GF)

end spec

end EtcdGrove
end Perennial
