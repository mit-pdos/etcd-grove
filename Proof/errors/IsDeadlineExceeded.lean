/-
The trust boundary: `errors.Is` at the target `context.DeadlineExceeded` (an empty struct, which
Perennial's `errors.wp_Is`, for pointer targets, does not take; the spec file says why it holds).
-/
module

public import Spec.errors.IsDeadlineExceeded

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
variable [package_sem : _root_.Perennial.errors.Assumptions]

axiom errors.IsDeadlineExceeded.wp_proof : errors.IsDeadlineExceeded.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
