/-
The trust boundary: `(*rate.Limiter).Reserve()` (`golang.org/x/time/rate` is names-only).
Lean-first.
(prove-metrics3, 2026-11-21) Not provable over the real code yet: the token bucket (`reserveN`) negates a
`float64` (`-tokens`), which Perennial's semantics does not step (`notes/perennial-changes.md`).
-/
module

public import Spec.golang_org.x.time.rate.Limiter__Reserve

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

axiom rate.Limiter.Reserve.wp_proof : rate.Limiter.Reserve.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
