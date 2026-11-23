/-
`(*rate.Reservation).Cancel()` (x/time/rate v0.16.0, `rate.go:160-163`: `CancelAt(time.Now())`;
rate-wait, 2026-11-23). Lean-first.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- **`r.Cancel()`**: `r.CancelAt(time.Now())`. -/
abbrev rate.Reservation.Cancel.spec : Prop :=
  ∀ (r : Loc) (rv : golang_org.x.time.rate.Reservation) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ r ↦{dq} rv ∗
      rate.limiterOk rv.lim' }}
    (App (Val (r @!! go.GoType.PointerType golang_org.x.time.rate.Reservation.ty @!! go!"Cancel"))
      (Val #()))
  {{ RET #(); r ↦{dq} rv }}

end spec

end EtcdGrove
end Perennial
