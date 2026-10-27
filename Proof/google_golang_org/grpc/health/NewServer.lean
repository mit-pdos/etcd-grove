/-
Trust boundary: `health.NewServer` (an axiom; see `Spec/google_golang_org/grpc/health/NewServer.lean`).
-/
module

public import Spec.google_golang_org.grpc.health.NewServer

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

/-- **Trust boundary** (item 4, the server start): grpc's `health.NewServer` allocates a `Server`
with its status map (`""` serving) and its mutex: non-nil; its methods lock the mutex, so they are
safe from any goroutine. -/
axiom health.NewServer.wp_proof : health.NewServer.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
