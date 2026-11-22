/-
`slices.Concat(ss...)` of string slices (Go's `slices`, names only in Perennial): **the trust
boundary**. The axiom (see its docstring for why it is faithful). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.slices.Concat

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

/-- **The trust boundary.** Go's `slices.Concat(slices...)` returns a new slice holding the elements of each slice in
turn, reading the slices only. Go panics (`len out of range`) when the total length overflows
`int` (`slices.go:491-498`, before `Grow`), so the spec takes the total `< 2 ^ 63`. Until
2026-11-22 it took no premise, arguing that the address space bounds the total; it does not, since
the inputs may alias (claim #26; `examples/premisefix/concatlen`). The statement is the string
instance of Perennial's proved `slices.Concat.spec` (mit-pdos/perennial#670), so the axiom becomes a
theorem after the pin bump. -/
axiom Concat.wp_proof : Concat.spec (GF := GF) (hG := hG)

end proof

end slices
end EtcdGrove
end Perennial
