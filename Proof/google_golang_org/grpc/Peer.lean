/-
**Trust boundary**: `grpc.Peer(p)` returns grpc's `PeerCallOption` for `p` (an axiom; see `Spec/google_golang_org/grpc/Peer.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.Peer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `grpc.Peer(p)` returns grpc's `PeerCallOption` for `p`. -/
axiom grpc.Peer.wp_proof : grpc.Peer.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
