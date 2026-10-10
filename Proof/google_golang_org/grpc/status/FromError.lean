/-
Trust boundary: `status.FromError` returns, and so does the `Code()` of the `*Status` it returns. (an axiom; see `Spec/google_golang_org/grpc/status/FromError.lean`).
-/
module

public import Spec.google_golang_org.grpc.status.FromError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `status.FromError` returns, and so does the `Code()` of the `*Status` it returns. -/
axiom status.FromError.wp_proof : status.FromError.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
