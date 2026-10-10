/-
`strings.Compare`: the trust boundary (see `Spec/strings/Compare.lean`). Perennial has no model
of Go's `strings.Compare` (`bytealg.CompareString`, assembly); a trusted model in Perennial, as
`strings.HasPrefix`'s, would replace this axiom.
-/
module

public import Spec.strings.Compare

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

/-- **Trust boundary**: `strings.Compare` compares bytewise. -/
axiom strings.Compare.wp_proof : strings.Compare.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
