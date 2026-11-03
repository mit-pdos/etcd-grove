/-
Proof of `Spec/k8s_io/client_go/tools/cache/ResourceEventHandlerFuncs__OnDelete.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Its body calls only the field's function (the precondition's contract).
-/
module

public import Spec.k8s_io.client_go.tools.cache.ResourceEventHandlerFuncs__OnDelete

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem ResourceEventHandlerFuncs.OnDelete.wp_proof :
    ResourceEventHandlerFuncs.OnDelete.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
