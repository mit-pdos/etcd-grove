/-
`fmt.Sprintf(format, ds, s)` of a slice of authorizer `Decision`s and a string: **the trust
boundary** (`UnconditionalPartsOrFailClosed`'s reason, `%v` of
`sets.List(d.PossibleDecisions())`). The axiom (see its docstring for why it is faithful).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.SprintfDecisions

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The trust boundary.** Go's `fmt.Sprintf` formats a `[]authorizer.Decision` (under any verb) by reading the
slice's elements and calling each one's `String()` (`Decision` has it, value receiver,
`interfaces.go`: a switch returning a literal, or `fmt.Sprintf("Unknown (%d)", int(d))`, no effect
and no panic), and a string by its bytes; it returns the result and writes nothing. The spec says
only that some string comes back (the model's `SprintfOut` is not claimed). -/
axiom fmt.SprintfDecisions.wp_proof : fmt.SprintfDecisions.spec (GF := GF) (hG := hG)

end proof


end EtcdGrove
end Perennial
