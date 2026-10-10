/-
Trust boundary: `strings.TrimPrefix` returns the string without the prefix, if it has it. (an axiom; see `Spec/strings/TrimPrefix.lean`).
-/
module

public import Spec.strings.TrimPrefix

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

/-- **Trust boundary**: `strings.TrimPrefix` returns the string without the prefix, if it has it. -/
axiom strings.TrimPrefix.wp_proof : strings.TrimPrefix.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
