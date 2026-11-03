/-
Proof of `Spec/k8s_io/client_go/tools/cache/NewReflectorWithOptions.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Missing callee specs (next round): `ToListerWatcherWithContext`, `wait.Backoff.DelayWithReset`,
`naming.GetNameFromCallsite`, `klog.LoggerWithName`, `getTypeDescriptionFromObject`,
`getExpectedGVKFromObject`, `features.FeatureGates().Enabled(WatchListClient)` (reads `false`:
a gate premise as `gateOk`), `math.Ceil`; `reflect.TypeOf` stronger than its boundary spec
(`typeOfOk`, as `InformerFor`'s).
-/
module

public import Spec.k8s_io.client_go.tools.cache.NewReflectorWithOptions
public import Spec.k8s_io.klog.v2.Background
public import Spec.reflect.TypeOf

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

theorem NewReflectorWithOptions.wp_proof
    (wp_TypeOf : reflect.TypeOf.spec (GF := GF) (hG := hG))
    (wp_Background : klog.Background.spec (GF := GF) (hG := hG)) :
    NewReflectorWithOptions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
