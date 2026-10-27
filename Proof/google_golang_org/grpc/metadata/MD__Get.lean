/-
The trust boundary: `metadata.MD.Get` (grpc's `metadata` is names-only).
-/
module

public import Spec.google_golang_org.grpc.metadata.MD__Get

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom metadata.MD.Get.wp_proof : metadata.MD.Get.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
