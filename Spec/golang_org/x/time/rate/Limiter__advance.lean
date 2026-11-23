/-
`lim.advance(t)` (x/time/rate v0.16.0, `rate.go:431-447`), with the limiter's mutex held: for
`reserveN` and `Reservation.CancelAt` (rate-wait, 2026-11-23: until then a private lemma of
`reserveN`'s proof). Lean-first.
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

/-- **`lim.advance(t)`**, with the fields it reads held (the limiter's mutex held): some `float64`
(the tokens the bucket would hold at `t`), the fields unchanged. -/
abbrev rate.Limiter.advance.spec : Prop :=
  ∀ (rl : Loc) (t : _root_.Perennial.time.Time) (l : golang_org.x.time.rate.Limit) (b tk : w64)
    (la : _root_.Perennial.time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗
      rl.[golang_org.x.time.rate.Limiter, go!"limit"] ↦ l ∗
      rl.[golang_org.x.time.rate.Limiter, go!"burst"] ↦ b ∗
      rl.[golang_org.x.time.rate.Limiter, go!"tokens"] ↦ tk ∗
      rl.[golang_org.x.time.rate.Limiter, go!"last"] ↦ la }}
    (App (Val (rl @!! go.GoType.PointerType golang_org.x.time.rate.Limiter.ty @!! go!"advance"))
      (Val #t))
  {{ (f : w64), RET #f;
      rl.[golang_org.x.time.rate.Limiter, go!"limit"] ↦ l ∗
      rl.[golang_org.x.time.rate.Limiter, go!"burst"] ↦ b ∗
      rl.[golang_org.x.time.rate.Limiter, go!"tokens"] ↦ tk ∗
      rl.[golang_org.x.time.rate.Limiter, go!"last"] ↦ la }}

end spec

end EtcdGrove
end Perennial
