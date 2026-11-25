/-
`grpc.NewClient(target, opts...)` (grpc's `clientconn.go`, names only; item 5, client construction): a
client connection, the producer of `grpcConn` (`Proof/google_golang_org/grpc/InvDial.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvDial

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`grpc.NewClient(target, opts...)`** with dial options doing `ds` (`dialOptsAt`), whose target
resolves to the addresses `addrs` (`dialTargetOk`: through the dial's one resolver `rb`, which resolves
the target's scheme to `addrs`, `grpcResolverAt`, taken: the resolver's state is the connection's from
then on; or through grpc's `passthrough` resolver to the one address of a `passthrough:///a` target),
returns a connection that reaches the servers at `addrs` (each attempt one of them) with the unary
interceptor chain the options set (`unaryIcsOf ds`: the last `WithUnaryInterceptor`'s) and no default
call options (`grpcConn`), dialed with the options `connOptsOf ds` (`grpcConnOpts`: its unary and stream
interceptors and per-RPC credentials, from which `ClientConn.NewStream` states its streams), or an error
(an unparsable target, no transport credentials, ...). Since the auth plan's C1 (2026-10-28): given the
contract `Q` of the per-RPC credentials the options add (`perRPCCredsOk`, for each of `credsOfDial ds`),
what they return to the connection's attempts (`connCredsOk`; every attempt is after the dial, so after
the contract holds). Since 2026-11-23 (#24's S2 signatures): the credentials' contract holds for the
resources of a family `Ok`, and the connection's calls take one of them from their callers
(`grpcConn … Ok`). (grpc-trusted-T, T7, 2026-11-24) Any stream interceptor (until then etcd's, and one,
`dialOk`), the passthrough resolver, and the connection's options in the post. -/
abbrev grpc.NewClient.spec : Prop :=
  ∀ (target : GoString) (sl : GoSlice) (ds : List GrpcDialOpt) (rb : GoInterface)
    (scheme : GoString) (addrs : List GoString) (Ok : IProp GF → Prop) (Q : GrpcMd → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ dialOptsAt sl ds ∗
      dialTargetOk ds target rb scheme addrs ∗
      [∗list] pc ∈ credsOfDial ds, perRPCCredsOk pc Ok Q }}
    (App (App (Val (@! google_golang_org.grpc.NewClient)) (Val #target)) (Val #sl))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      (⌜err = GoInterface.nil⌝ ∗ grpcConn conn addrs (unaryIcsOf ds) [] Ok ∗
          connCredsOk conn (credsOfDial ds) Q ∗ grpcConnOpts conn (connOptsOf ds)) ∨
        ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
