/-
The trust boundary: `(*time.Duration).Seconds` (the pointer wrapper of `Duration.Seconds`, a float
division outside Perennial's `time` model, untranslated as the method itself; total).
-/
module

public import Spec.time.Duration__Seconds_ptr

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

axiom time.Duration.Seconds_ptr.wp_proof : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
