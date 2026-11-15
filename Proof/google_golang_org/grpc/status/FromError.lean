/-
Trust boundary: `status.FromError` of an error grpc accepts returns, and so do the `Code()` and
`Message()` of the `*Status` it returns (an axiom; see `Spec/google_golang_org/grpc/status/FromError.lean`).
-/
module

public import Spec.google_golang_org.grpc.status.FromError

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

/-- **Trust boundary**: `status.FromError` of an error grpc accepts returns, and so do the
`Code()` and `Message()` of the `*Status` it returns. `FromError` reads the `*Status` the error's
`GRPCStatus()` returns (through `Proto()`, `Code()`): justified by the premise, whose
`grpcErrMethodsOk` gives that status read-only (`grpcStatusRO`, E1, 2026-11-15; it was a latent
assumption, `notes/axiom-review/grpc-status-immutability.md`). -/
axiom status.FromError.wp_proof : status.FromError.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
