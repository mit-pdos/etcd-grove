/-
The trust boundary: `time.Time.IsZero` (a test of the time's fields, outside Perennial's `time` translation; total; unit P1b).
-/
module

public import Spec.time.Time__IsZero

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom time.Time.IsZero.wp_proof : time.Time.IsZero.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
