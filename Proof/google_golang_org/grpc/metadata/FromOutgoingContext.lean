/-
The trust boundary: `metadata.FromOutgoingContext` (grpc's `metadata` is names-only).
-/
module

public import Spec.google_golang_org.grpc.metadata.FromOutgoingContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom metadata.FromOutgoingContext.wp_proof :
  metadata.FromOutgoingContext.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
