/-
`e.Unwrap()` on an `*OpError` `pe` (translated, `net.go`: `return e.Err`): its `Err`. What
`errors.Is` and `errors.As` walk through. Proved in `Net/Proof/net/OpError__Unwrap.lean`.
-/
module

public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev OpError.Unwrap.spec : Prop :=
  ∀ (pe : Loc) (v : net.OpError),
  {{ (pe ↦□ v : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType OpError.ty) go!"Unwrap" #pe)) (Val #()))
  {{ RET #v.Err'; True }}

end spec

end net
end Perennial
