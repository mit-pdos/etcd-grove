/-
Proof of `Spec/k8s_io/client_go/util/workqueue/rateLimitingType__Add.lean`: **blocked, gap C2** (the method has
no translation to unfold: `notes/k8s-clientgo-goose.md`). With the translator's fix it is the
wrapper's load of the embedded field (`StructFieldRef (rateLimitingType.ty T) "TypedDelayingInterface"`, read-only for
good in `isRateLimitingQueue`) and `delayingType.Add`'s spec. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__Add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem rateLimitingType.Add.wp_proof : rateLimitingType.Add.spec (GF := GF) (hG := hG) := by
  sorry -- gap C2: no `MethodUnfold` for the promoted method

end proof

end workqueue
end EtcdGrove
end Perennial
