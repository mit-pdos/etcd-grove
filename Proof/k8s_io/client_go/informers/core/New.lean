/-
Proof of `Spec/k8s_io/client_go/informers/core/New.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Its body calls nothing (a struct literal). Not provable at the current translation: its
result type `informers/core.Interface` is names only (`Interface.underlying` an axiom), so the
conversion of the `*group` to it is stuck (a translation gap, the run's report).
-/
module

public import Spec.k8s_io.client_go.informers.core.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informerscore

open Iris Iris.BI apimodel cache informer informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.core.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem New.wp_proof :
    New.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end informerscore
end EtcdGrove
end Perennial
