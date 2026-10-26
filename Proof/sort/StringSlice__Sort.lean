/-
The trust boundary: `sort.StringSlice.Sort` (Perennial models `sort.StringSlice`'s type only; why
the statement is true is in its spec's docstring).
-/
module

public import Spec.sort.StringSlice__Sort

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

axiom sort.StringSlice.Sort.wp_proof : sort.StringSlice.Sort.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
