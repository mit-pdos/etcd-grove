/-
Proof of `Spec/google_golang_org/grpc/Peer.lean` over the real body (prove-grpcsmall, 2026-11-20; a
trust-boundary axiom while grpc's `Peer` was names only): grpc's `rpc_util.go` returns
`PeerCallOption{PeerAddr: p}` as a `CallOption`, which is what `grpcPeerOpt` (a definition since
then, `Proof/google_golang_org/grpc/InvGrpc.lean`) says.
-/
module

public import Spec.google_golang_org.grpc.Peer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem grpc.Peer.wp_proof : grpc.Peer.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  wp_auto
  iapply HΦ
  ipureintro
  rfl

end proof

end EtcdGrove
end Perennial
