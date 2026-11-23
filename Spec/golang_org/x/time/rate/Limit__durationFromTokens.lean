/-
`limit.durationFromTokens(tokens)` (x/time/rate v0.16.0, `rate.go:458-471`), for `reserveN` and
`Reservation.CancelAt` (rate-wait, 2026-11-23: until then a private lemma of `reserveN`'s proof).
Lean-first.
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

/-- **`limit.durationFromTokens(tokens)`**: some duration (`InfDuration` for a non-positive `limit`
or a duration above `MaxInt64`, else `time.Duration` of the float, which Go converts without a panic
whatever its value). -/
abbrev rate.Limit.durationFromTokens.spec : Prop :=
  ∀ (l : golang_org.x.time.rate.Limit) (f : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate }}
    (App (Val (l @!! golang_org.x.time.rate.Limit.ty @!! go!"durationFromTokens")) (Val #f))
  {{ (d : _root_.Perennial.time.Duration), RET #d; True }}

end spec

end EtcdGrove
end Perennial
