/-
The trust boundary: `strconv.FormatBool` (Perennial's `strconv` is names-only; `FormatBool` is total).
-/
module

public import Spec.strconv.FormatBool

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

axiom strconv.FormatBool.wp_proof : strconv.FormatBool.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
