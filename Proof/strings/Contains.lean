/-
The trust boundary of `strings.Contains` (see its spec).
-/
module

public import Spec.strings.Contains

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
axiom strings.Contains.wp_proof : strings.Contains.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
