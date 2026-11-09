/-
`(*grpc.ClientConn).Invoke(ctx, method, req, reply, opts...)` (grpc-go, assumed: `call.go`).

Users: every generated unary stub (`etcdserverpb.kVClient.Range`, ..., 3h), hence every unary call
of the client (W0's `RemoteKV.*Triple`, 1c's `RemoteCallTriple`).

Why true: `Invoke` combines the connection's default call options (none for etcd's connection)
with `opts` and calls the unary interceptor, if one was dialed, with grpc's own `invoke` as the
invoker; else `invoke` itself. `invoke` makes one attempt (`attemptOk_call`): it picks a ready
transport to an address its resolver reported, sends the request once (grpc-go's transparent
retry resends only a stream that never reached the server's handler: no run is duplicated), and
returns the reply or the status the server sent, or an error of its own.

Proof sketch of 1c's `AttemptTriple` from it (the realization of W0's at-most-once): the invoker is
`inv` with `attemptOk cc A R inv`; the method's contract at every address the client's resolver
reports is `V3rpc.etcdUnary γ m` (`servesAt γ ep`, which V3rpc's `servesAt_addr` makes `addrAt ep (etcdContract γ ep)`, whose
entry for `m` is `etcdUnary γ ep m`; verify-round, A1-C S4: it cited a nonexistent `servesAt_serves`); the caller builds
`S md (norm c) Φ` from its update (the member decodes the wire view, 3h's `holds_norm`) and `R` (its token's principal), `Φ` mapping the outcome to the four
cases of `AttemptTriple`.

Changes: from `specs-ref/Spec/google_golang_org/grpc/ClientConn__Invoke.lean`: the attempt is over
the method's registered contract and message contents (`attemptOk`), not over a caller-chosen
`ProtoMsg` (`notes/grpc-msg-models.md`); no size premise (`msgsFit` is the connection's).

Margin: the code's errors carry more (codes of its own errors) than `ownErr` says.
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

/-- `cc.Invoke(ctx, method, req, reply, opts...)`: the connection's unary interceptor around grpc's
invoker (WP form, for any postcondition). -/
def ClientConn.Invoke.spec : Prop :=
  ∀ (cc : Loc) (A : GoString → IProp GF) (ui si : Option val) (R : MD → IProp GF)
    (ctx : GoInterface) (m : GoString) (req reply : GoInterface) (opts : GoSlice)
    (Ψ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ connAt cc A ui si R ∗
    (∀ inv : val, attemptOk cc A R inv -∗
      match ui with
      | none => WP (App (App (App (App (App (App (Val inv) (Val #ctx)) (Val #m)) (Val #req))
          (Val #reply)) (Val #cc)) (Val #opts)) {{ Ψ }}
      | some f => WP (App (App (App (App (App (App (App (Val f) (Val #ctx)) (Val #m)) (Val #req))
          (Val #reply)) (Val #cc)) (Val inv)) (Val #opts)) {{ Ψ }}) ⊢
  WP (App (App (App (App (App (Val (cc @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"Invoke"))
    (Val #ctx)) (Val #m)) (Val #req)) (Val #reply)) (Val #opts)) {{ Ψ }}

end spec

end Grpc
end EtcdGrove
end Perennial
