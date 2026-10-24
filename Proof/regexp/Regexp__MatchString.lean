/-
The trust boundary: `regexp.Regexp.MatchString` (`regexp` is names-only).
-/
module

public import Spec.regexp.Regexp__MatchString

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

axiom regexp.Regexp.MatchString.wp_proof : regexp.Regexp.MatchString.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
