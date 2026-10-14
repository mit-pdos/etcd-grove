/-
The trust boundary: `utf8.ValidString` (Go's `unicode/utf8`, which Perennial does not translate:
names-only here).
-/
module

public import Spec.unicode.utf8.ValidString

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

axiom utf8.ValidString.wp_proof : utf8.ValidString.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
