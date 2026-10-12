/-
The trust boundary: `status.Errorf` (grpc is names-only; as `status.Error`).
-/
module

public import Spec.google_golang_org.grpc.status.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom status.Errorf.wp_proof : status.Errorf.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
