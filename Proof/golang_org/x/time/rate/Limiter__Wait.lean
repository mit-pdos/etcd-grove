/-
The trust boundary: `(*rate.Limiter).Wait` (`golang.org/x/time/rate` is names-only).
(prove-metrics3, 2026-11-21) Not provable over the real code then: the token bucket (`reserveN`) negates a
`float64` (`-tokens`), which Perennial's semantics did not step. (prove-metrics-float, 2026-11-22) The
bucket is now proved (`rate.Limiter.reserveN.wp_proof`, over Perennial's IEEE 754 floats); what keeps
`Wait` an axiom is the rest of `wait` (`rate.go:262-316`), none of it float-dependent but `CancelAt`:
`fmt.Errorf` (rate would import `fmt`), the non-blocking and blocking `select`s on `ctx.Done()`, the
timer closure, and `Reservation.CancelAt` (the limiter's mutex through the reservation's `lim`).
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

axiom rate.Limiter.Wait.wp_proof : rate.Limiter.Wait.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
