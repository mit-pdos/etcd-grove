/-
Proof of `Spec/k8s_io/client_go/util/workqueue/noMetrics__updateUnfinishedWork.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.noMetrics__updateUnfinishedWork

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

theorem noMetrics.updateUnfinishedWork.wp_proof : noMetrics.updateUnfinishedWork.spec (GF := GF) (hG := hG) := by
  intro K T _ v 
  wp_start
  wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
