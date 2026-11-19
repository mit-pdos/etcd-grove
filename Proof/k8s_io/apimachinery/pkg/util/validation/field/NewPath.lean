/-
`field.NewPath(name, moreNames...)` (apimachinery, names only): **the trust boundary**. The axiom
(see its docstring for why it is faithful). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.NewPath

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The trust boundary.** `NewPath(name, moreNames...)` (`path.go`) allocates a `*Path` for `name` and a child for
each of `moreNames`, reading that slice only. No panic. -/
axiom NewPath.wp_proof : NewPath.spec (GF := GF) (hG := hG)

end proof

end field
end EtcdGrove
end Perennial
