/-
Proof of `Spec/k8s_io/client_go/util/workqueue/noMetrics__add.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.noMetrics__add

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

theorem noMetrics.add.wp_proof : noMetrics.add.spec (GF := GF) (hG := hG) := by
  intro K T _ v k
  wp_start
  wp_auto
  wp_end

end proof

end workqueue
end EtcdGrove
end Perennial
