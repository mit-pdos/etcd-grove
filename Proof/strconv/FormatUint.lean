/-
The trust boundary: `strconv.FormatUint` (Perennial's `strconv` is names-only; `FormatUint` is total: the decimal digits).
-/
module

public import Spec.strconv.FormatUint

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

axiom strconv.FormatUint.wp_proof : strconv.FormatUint.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
