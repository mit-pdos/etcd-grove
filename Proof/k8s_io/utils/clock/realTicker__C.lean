/-
The trust boundary: `Spec/k8s_io/utils/clock/realTicker__C.lean`. Lean-first.
-/
module

public import Spec.k8s_io.utils.clock.realTicker__C

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

axiom clock.realTicker.C.wp_proof : clock.realTicker.C.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
