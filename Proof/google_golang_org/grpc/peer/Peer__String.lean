/-
**Trust boundary**: `(*peer.Peer).String()` of a peer grpc wrote (or the zero peer) returns (an axiom; see `Spec/google_golang_org/grpc/peer/Peer__String.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.peer.Peer__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [peer_sem : google_golang_org.grpc.peer.Assumptions]

/-- **Trust boundary**: `(*peer.Peer).String()` of a peer grpc wrote (or the zero peer) returns. -/
axiom peer.Peer.String.wp_proof : peer.Peer.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
