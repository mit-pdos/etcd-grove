/-
The trust boundary: `metadata.FromIncomingContext` (grpc's `metadata` is names-only).
-/
module

public import Spec.google_golang_org.grpc.metadata.FromIncomingContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom metadata.FromIncomingContext.wp_proof : metadata.FromIncomingContext.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
