/-
`grpc.Peer(p)` (grpc-go, assumed: `rpc_util.go`).

Users: the client's retry interceptor (`retry_interceptor.go:46-47`, every unary call, 1c: the
peer logged on a retry).

Why true: a `PeerCallOption{PeerAddr: p}`; after an attempt grpc writes `*p` (the peer's
`*peer.Peer`, `call.go`'s `after` hooks), under no lock of the caller's: the variable is lent to
grpc from then on. The spec puts it in an invariant (`peerVar`: a `nil` or a `peerOk` pointer),
which grpc's writes keep and the caller's reads use.

Changes: restored (round 1), with the ownership of `p` (the old spec gave nothing for it).

Margin: the caller may not write `p` again.
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

/-- `grpc.Peer(p)` of an owned peer variable: a call option, the variable lent to grpc
(`peerVar`). -/
def Peer.spec : Prop :=
  ∀ (p q : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ p ↦ q ∗ ⌜q = null⌝ }}
    (App (Val (@! google_golang_org.grpc.Peer)) (Val #p))
  {{ (v : GoInterface), RET #v; callOptOk v ∗ peerVar p }}

end spec

end Grpc
end EtcdGrove
end Perennial
