/-
The trust boundary: `(*rate.Reservation).Delay()` (`golang.org/x/time/rate` is names-only).
Lean-first.
-/
module

public import Spec.golang_org.x.time.rate.Reservation__Delay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom rate.Reservation.Delay.wp_proof : rate.Reservation.Delay.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
