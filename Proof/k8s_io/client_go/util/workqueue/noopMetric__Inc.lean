/-
Proof of `Spec/k8s_io/client_go/util/workqueue/noopMetric__Inc.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.noopMetric__Inc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem noopMetric.Inc.wp_proof : noopMetric.Inc.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start
  wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
