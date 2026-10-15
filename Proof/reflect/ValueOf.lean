/-
The trust boundary: `reflect.ValueOf` (names-only; Go reflection), of an interface holding a
pointer, with the `IsNil()` of its result. Unit P4 (2026-10-14).
-/
module

public import Spec.reflect.ValueOf

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

axiom reflect.ValueOf.wp_proof : reflect.ValueOf.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
