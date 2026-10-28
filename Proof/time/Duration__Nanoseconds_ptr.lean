/-
The trust boundary: `(*time.Duration).Nanoseconds()` (untranslated in Perennial's `time`; it is
`int64(*l)`). Lean-first.
-/
module

public import Spec.time.Duration__Nanoseconds_ptr

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

axiom time.Duration.Nanoseconds_ptr.wp_proof : time.Duration.Nanoseconds_ptr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
