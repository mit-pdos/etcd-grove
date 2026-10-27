/-
The trust boundary: `Spec/k8s_io/utils/clock/realTimer__Stop.lean`. Lean-first.
-/
module

public import Spec.k8s_io.utils.clock.realTimer__Stop

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

axiom clock.realTimer.Stop.wp_proof : clock.realTimer.Stop.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
