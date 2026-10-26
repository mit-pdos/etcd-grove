/-
Proof of `Spec/google_golang_org/grpc/NewClient.lean`: a trust-boundary axiom (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.NewClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 5): grpc's `NewClient` (`clientconn.go`, v1.84.0, the version etcd's
`go.mod` pins). It builds `dialOptions` by applying each option in order (so the last
`WithUnaryInterceptor` sets `unaryInt`, `chainUnaryClientInterceptors` puts it first and appends
`chainUnaryInts`, which no descriptor sets: `unaryIcsOf`), parses the target, looks its scheme up in
the dial's resolvers (`getResolver`: the `WithResolvers` builders first) and returns the
`ClientConn` (idle: it connects on the first RPC) or an error; the resolver, built by grpc on
the first RPC, reports the address `addr`, the one subchannel the RPCs go to (the round-robin
policy etcd's resolver configures, over one address). What a connection's RPCs do is
`ClientConn.Invoke`'s and `NewStream`'s axioms (which assume etcd's stream interceptor:
`dialOk`). -/
axiom grpc.NewClient.wp_proof : grpc.NewClient.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
