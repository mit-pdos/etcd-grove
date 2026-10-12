/-
The trust boundary: `context.WithValue` (Perennial translates `context` without `WithValue`'s body).
-/
module

public import Spec.context.WithValue

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
variable [package_sem : context.Assumptions]

axiom context.WithValue.wp_proof : context.WithValue.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
