/-
The trust boundary: `rand.Int31` (`math/rand` is names-only in Perennial).
-/
module

public import Spec.math.rand.Int31

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom rand.Int31.wp_proof : rand.Int31.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
