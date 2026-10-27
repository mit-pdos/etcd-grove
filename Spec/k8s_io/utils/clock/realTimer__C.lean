/-
`(*clock.realTimer).C()` (`k8s.io/utils/clock`, names-only here: the trust boundary; it is
`r.timer.C`). Lean-first.
-/
module

public import Spec.k8s_io.utils.clock.RealClock__NewTimer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `r.C()`: the timer's channel, on which a receive may yield some time (Perennial's timers). -/
abbrev clock.realTimer.C.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock ∗ clock.realTimerOk p }}
    (App (Val (p @!! go.GoType.PointerType k8s_io.utils.clock.realTimer.ty @!! go!"C")) (Val #()))
  {{ (ch : Loc) (γ : ChanNames), RET #ch; isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }}

end spec

end EtcdGrove
end Perennial
