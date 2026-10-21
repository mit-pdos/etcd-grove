/-
**The client side of the gRPC trust boundary** (2026-10-14, generic: any unary method, any
connection; an axiom: `Proof/google_golang_org/grpc/ClientConn__Invoke.lean`): grpc's
`(*ClientConn).Invoke` runs the connection's unary interceptor chain over grpc's own `invoke`.
Unit P3a moved the boundary below the interceptors: it was a contract of `Invoke` with etcd's
retry interceptor inside (unit C1, then the generic contract of the same day); the interceptor is
now proved (`client/v3/Client__unaryClientInterceptor.lean`) and the contract of `Invoke` on an
etcd client's connection a theorem (`client/v3/EtcdInvoke.lean`). Lean-first (no Rocq
counterpart; the shape is Grove's urpc's); the design: `notes/decisions.md`, "A generic gRPC
specification" and "The retry interceptor proved: the gRPC boundary below it".
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [peer_sem : google_golang_org.grpc.peer.Assumptions]

/-- **`conn.Invoke(ctx, method, req, reply, opts...)`** on a connection with the unary interceptor
chain `ics` and the default call options `dopts` (`grpcConn conn addrs ics dopts`, grpc's
`call.go`): with the call options `combine(dopts, opts)` (a slice holding `dopts ++ vs`: `opts`
itself if `dopts` is empty), the chain over grpc's `invoke` (`chainWP`: the first interceptor
called with an invoker that runs the rest; with no interceptor, `invoke` itself), where `invoke`
makes one attempt (`grpcInvokerOk conn addrs`: a run of the handler served for the method at one
of `addrs`, or an error). Stated as a weakest precondition, for any postcondition `Ψ`: the call's behavior is the
chain's. -/
abbrev grpc.ClientConn.Invoke.spec : Prop :=
  ∀ (conn : Loc) (addrs : List GoString) (ics : List GoFunc) (dopts : List GoInterface)
    (ctx : GoInterface) (method : GoString) (req reply : GoInterface) (opts : GoSlice)
    (vs : List GoInterface) (Ψ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ grpcConn conn addrs ics dopts ∗
      opts ↦*□ vs ∗
      (∀ (inv : GoFunc) (opts' : GoSlice), grpcInvokerOk conn addrs inv -∗
        opts' ↦*□ (dopts ++ vs) -∗ chainWP conn ics inv #ctx #method #req #reply #opts' Ψ) ⊢
    WP (App (App (App (App (App
      (Val (conn @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Invoke"))
      (Val #ctx)) (Val #method)) (Val #req)) (Val #reply)) (Val #opts)) {{ Ψ }}

end spec

end EtcdGrove
end Perennial
