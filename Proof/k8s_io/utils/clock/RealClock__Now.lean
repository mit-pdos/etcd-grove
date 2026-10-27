/-
The trust boundary: `Spec/k8s_io/utils/clock/RealClock__Now.lean`. Lean-first.
-/
module

public import Spec.k8s_io.utils.clock.RealClock__Now

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

axiom clock.RealClock.Now.wp_proof : clock.RealClock.Now.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
