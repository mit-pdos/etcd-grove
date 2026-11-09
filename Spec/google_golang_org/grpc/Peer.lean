/-
`grpc.Peer(p)` (grpc-go, assumed: `rpc_util.go:312-331`).

Users: the client's retry interceptor (`client/v3/retry_interceptor.go:46-47`, every unary call,
1c: `var p peer.Peer; grpcOpts = append(grpcOpts, grpc.Peer(&p))`, the peer logged on a retry,
`p.String()` at `:71`, `peer.Peer.String.spec`).

Why true: it returns `PeerCallOption{PeerAddr: p}`; after an attempt grpc runs
`if x, ok := peer.FromContext(...); ok { *o.PeerAddr = *x }`, copying the transport's peer (whose
fields print: `peer/Api.lean`) into the struct variable. The variable is lent to grpc from then on:
an invariant holds its fields, each one that prints (`peerVar_inv`), which grpc's field stores keep
and the caller's field loads use.

Changes: verify-round: over the struct variable `p ↦ v` (A6 completeness F3: was `p ↦ q` with
`q : Loc`, a `*peer.Peer` variable, which the caller's `var p peer.Peer` is not), its fields
printing (`peerFieldsOk`: the zero peer's do, `peer_nil`).

Margin: the caller may not write `p` again.
-/
module

public import Spec.google_golang_org.grpc.peer.Api

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

/-- `grpc.Peer(&p)` of an owned `peer.Peer` variable whose fields print: a call option, the
variable lent to grpc (`peerVar`). -/
def Peer.spec : Prop :=
  ∀ (p : Loc) (v : google_golang_org.grpc.peer.Peer),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ p ↦ v ∗ peerFieldsOk v }}
    (App (Val (@! google_golang_org.grpc.Peer)) (Val #p))
  {{ (o : GoInterface), RET #o; callOptOk o ∗ peerVar p }}

end spec

end Grpc
end EtcdGrove
end Perennial
