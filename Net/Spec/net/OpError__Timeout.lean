/-
`e.Timeout()` on an `*OpError` `pe` (`OpError.Timeout.impl`, `Net/TrustedCode/net.lean`, D14):
`false` if its `Err` is `poll.ErrNetClosing`'s type (`net.ErrClosed`), `true` if it is
`*poll.DeadlineExceededError` (`os.ErrDeadlineExceeded`) or `*timeoutError` (`errTimeout`), any
answer otherwise (`ErrFlag`; an `*os.SyscallError` answers its `Errno`'s, true for `ETIMEDOUT`).
Proved in `Net/Proof/net/OpError__Timeout.lean`.
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
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev OpError.Timeout.spec : Prop :=
  ∀ (pe : Loc) (v : net.OpError),
  {{ (pe ↦□ v : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType OpError.ty) go!"Timeout" #pe)) (Val #()))
  {{ (b : Bool), RET #b; ⌜ErrFlag v.Err' b⌝ }}

end spec

end net
end Perennial
