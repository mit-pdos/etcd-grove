/-
`e.Temporary()` on an `*OpError` `pe` (Go's `OpError.Temporary`, translated since S6; D14), whose
`Err` is one of net's own errors (`opErrOk`, the precondition approved by Upamanyu, D2): as
`Timeout` (`ErrFlag`: `false` for `net.ErrClosed`'s type, `true` for the deadline's and
`errTimeout`'s, any answer otherwise; an accept's `ECONNRESET` is temporary). Proved in
`Net/Proof/net/OpError__Temporary.lean`.
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
abbrev OpError.Temporary.spec : Prop :=
  ∀ (pe : Loc) (v : net.OpError),
  {{ (pe ↦□ v : IProp GF) ∗ opErrOk v }}
    (App (Val #(methods (go.GoType.PointerType OpError.ty) go!"Temporary" #pe)) (Val #()))
  {{ (b : Bool), RET #b; ⌜ErrFlag v.Err' b⌝ }}

end spec

end net
end Perennial
