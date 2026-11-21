/-
The trust boundary: `(*rate.Limiter).Wait` (`golang.org/x/time/rate` is names-only).
(prove-metrics3, 2026-11-21) Not provable over the real code yet: the token bucket (`reserveN`) negates a
`float64` (`-tokens`), which Perennial's semantics does not step (`notes/perennial-changes.md`).
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
