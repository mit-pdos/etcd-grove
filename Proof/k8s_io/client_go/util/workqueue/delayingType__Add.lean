/-
Proof of `Spec/k8s_io/client_go/util/workqueue/delayingType__Add.lean`: **blocked, gap C2** (the method has
no translation to unfold: `notes/k8s-clientgo-goose.md`). With the translator's fix it is the
wrapper's load of the embedded field (`StructFieldRef (delayingType.ty T) "TypedInterface"`, read-only for
good in `isDelaying`) and `Typed.Add`'s spec. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.delayingType__Add

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

theorem delayingType.Add.wp_proof : delayingType.Add.spec (GF := GF) (hG := hG) := by
  sorry -- gap C2: no `MethodUnfold` for the promoted method

end proof

end workqueue
end EtcdGrove
end Perennial
