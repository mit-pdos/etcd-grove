/-
`peer.FromContext(ctx)` (grpc-go, assumed: `peer/peer.go`).

Users: `v3rpc.logUnaryRequestStats` (`interceptor.go:107`: the remote address, logged).

Why true: it reads the run's context value (`ctx.Value(peerKey{})`), set by grpc's server for
every run, and returns it.

Changes: from `specs-ref/Spec/google_golang_org/grpc/peer/Peer__String.lean`'s neighbor.

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api
public import SpecPlan.Spec.PkgInit.google_golang_org.grpc.peer
public import GeneratedProof.google_golang_org.grpc.peer

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

/-- `peer.FromContext(ctx)` of a run's context: a peer whose address prints, or none. -/
def FromContext.spec : Prop :=
  ∀ (ctx : GoInterface) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.peer ∗ rpcCtx ctx md }}
    (App (Val (@! google_golang_org.grpc.peer.FromContext)) (Val #ctx))
  {{ (p : Loc) (ok : Bool), RET (PairV #p #ok); ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ peerOk p) }}

end spec

end Grpc
end EtcdGrove
end Perennial
