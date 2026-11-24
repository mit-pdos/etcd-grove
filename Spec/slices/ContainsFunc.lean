/-
`slices.ContainsFunc(s, f)`: proved (`Proof/slices/ContainsFunc.lean`) over Perennial's spec of its
translation (since Perennial 52d62e83c; until then names only, and this the trust boundary). Lean-first (no Rocq counterpart).
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
abbrev ContainsFunc.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {E : go.GoType} [IntoValTyped (GF := GF) V E] (s : GoSlice) (dq : DFrac) (xs : List V) (f : GoFunc),
  {{ s ↦*{dq} xs ∗
      □ (∀ (x : V), ⌜x ∈ xs⌝ -∗
        {{ (True : IProp GF) }} (App (Val #f) (Val #x)) {{ (b : Bool), RET #b; True }}) }}
    (App (App (Val #(functions _root_.Perennial.slices.ContainsFunc [go.GoType.SliceType E, E]))
      (Val #s)) (Val #f))
  {{ (b : Bool), RET #b; s ↦*{dq} xs }}

end spec

end slices
end EtcdGrove
end Perennial
