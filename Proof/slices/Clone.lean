/-
`slices.Clone(s)` (Go's `slices`, names only in Perennial): **the trust boundary**. The axiom (see
its docstring for why it is faithful). Lean-first (no Rocq counterpart).
-/
module

public import Spec.slices.Clone

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

/-- **The trust boundary.** Go's `slices.Clone(s)` (go1.22+: `append(s[:0:0], s...)`) returns a new slice holding
the elements of `s` (a shallow copy; `nil` for a `nil` `s`, whose points-to of `[]` holds), with its
whole capacity owned, and only reads `s`. It does not panic: the copy's length is `s`'s, which is in
memory. -/
axiom Clone.wp_proof : Clone.spec (GF := GF) (hG := hG)

end proof

end slices
end EtcdGrove
end Perennial
