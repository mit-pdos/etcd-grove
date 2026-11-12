/-
The trust boundary of `strconv.ParseInt` (see its spec).
-/
module

public import Spec.strconv.ParseInt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom strconv.ParseInt.wp_proof : strconv.ParseInt.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
