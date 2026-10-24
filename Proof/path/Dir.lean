/-
The trust boundary: `path.Dir` (`path` is names-only).
-/
module

public import Spec.path.Dir

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

axiom path.Dir.wp_proof : path.Dir.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
