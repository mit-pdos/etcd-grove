/-
`slices.Clone(s)`: an instance of Perennial's `slices.Clone.spec`, proved in `Proof/slices/Clone.lean`
(mit-pdos/perennial#670). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.GeneratedProof.slices

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace slices

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev Clone.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {E : go.GoType} [IntoValTyped (GF := GF) V E] (s : GoSlice) (dq : DFrac) (xs : List V),
  {{ (s ↦*{dq} xs : IProp GF) }}
    (App (Val #(functions _root_.Perennial.slices.Clone [go.GoType.SliceType E, E])) (Val #s))
  {{ (s' : GoSlice), RET #s'; s ↦*{dq} xs ∗ s' ↦* xs ∗ ownSliceCap V s' (DFrac.own 1) }}

end spec

end slices
end EtcdGrove
end Perennial
