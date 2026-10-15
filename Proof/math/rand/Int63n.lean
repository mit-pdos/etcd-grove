/-
The trust boundary: `rand.Int63n` (`math/rand` is names-only in Perennial).
-/
module

public import Spec.math.rand.Int63n

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

axiom rand.Int63n.wp_proof : rand.Int63n.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
