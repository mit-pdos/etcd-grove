/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedProcessor__run.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Missing callee specs (next round): `processorListener.watchSynced`, `sync.Cond.Signal`
(Perennial's), the run hook's `atomic.Pointer.Load`.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedProcessor__run
public import Spec.k8s_io.apimachinery.pkg.util.wait.Group__Start
public import Spec.k8s_io.client_go.tools.cache.processorListener__pop
public import Spec.k8s_io.client_go.tools.cache.processorListener__run

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

theorem sharedProcessor.run.wp_proof
    (wp_Group_Start : wait.Group.Start.spec (GF := GF) (hG := hG))
    (wp_run : cache.processorListener.run.spec (GF := GF) (hG := hG))
    (wp_pop : cache.processorListener.pop.spec (GF := GF) (hG := hG)) :
    sharedProcessor.run.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
