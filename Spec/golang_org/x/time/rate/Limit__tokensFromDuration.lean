/-
`limit.tokensFromDuration(d)` (x/time/rate v0.16.0, `rate.go:451-456`): the bucket's float
arithmetic, for `reserveN` and `Reservation.CancelAt` (rate-wait, 2026-11-23: until then a private
lemma of `reserveN`'s proof). Lean-first.
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

/-- **`limit.tokensFromDuration(d)`**: some `float64` (`d.Seconds() * float64(limit)`, or `0` for a
non-positive `limit`; no float operation panics in Go). -/
abbrev rate.Limit.tokensFromDuration.spec : Prop :=
  ∀ (l : golang_org.x.time.rate.Limit) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate }}
    (App (Val (l @!! golang_org.x.time.rate.Limit.ty @!! go!"tokensFromDuration")) (Val #d))
  {{ (f : w64), RET #f; True }}

end spec

end EtcdGrove
end Perennial
