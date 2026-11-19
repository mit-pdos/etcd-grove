/-
`field.ErrorList.ToAggregate()` (apimachinery, names only): **the trust boundary**. The axiom (see
its docstring for why it is faithful). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorList__ToAggregate

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

/-- **The trust boundary.** `list.ToAggregate()` (`errors.go`) returns `nil` for an empty list, else an aggregate of
the list's errors' messages deduplicated (it calls each `*Error`'s `Error()`, which formats the
error's fields, and `utilerrors.NewAggregate`); it reads the list only. The errors here are the
ones `IsDomainPrefixedKey` returns, well-formed `*field.Error`s. No panic. -/
axiom ErrorList.ToAggregate.wp_proof : ErrorList.ToAggregate.spec (GF := GF) (hG := hG)

end proof

end field
end EtcdGrove
end Perennial
