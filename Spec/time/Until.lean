/-
`time.Until(t)` (Perennial translates it with its body and has no spec of it; a candidate for
Perennial, `notes/perennial-changes.md`): some duration (`t.Sub(Now())`, or the current monotonic
reading subtracted from `t`'s). Called by the grpc model's `createHeaderFields` (the `grpc-timeout`
field). Stated as Perennial's `time.Since.spec`. Proved in `Proof/time/Until.lean`.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- See the file header. -/
abbrev time.Until.spec : Prop :=
  ∀ (t : _root_.Perennial.time.Time),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (Val (@! _root_.Perennial.time.Until)) (Val #t))
    {{ (d : w64), RET #d; True }}

end spec

end EtcdGrove
end Perennial
