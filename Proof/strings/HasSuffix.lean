/-
The trust boundary of `strings.HasSuffix` (see its spec).
-/
module

public import Spec.strings.HasSuffix

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
axiom strings.HasSuffix.wp_proof : strings.HasSuffix.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
