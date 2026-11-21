/-
`slices.ContainsFunc(s, f)` (Go's `slices`, names only in Perennial): **the trust boundary**. The
axiom (see its docstring for why it is faithful). Lean-first (no Rocq counterpart).
-/
module

public import Spec.slices.ContainsFunc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace slices

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The trust boundary.** Go's `slices.ContainsFunc(s, f)` (`IndexFunc(s, f) >= 0`) calls `f` on the elements of `s`
in order until one returns `true`, reading `s` only, and returns whether one did. The spec asks that
`f` can be called on every element (persistently) and says only that some boolean comes back. -/
axiom ContainsFunc.wp_proof : ContainsFunc.spec (GF := GF) (hG := hG)

end proof

end slices
end EtcdGrove
end Perennial
