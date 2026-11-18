/-
Proof of `Spec/k8s_io/apiserver/pkg/util/flowcontrol/WatchInitialized.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.util.flowcontrol.WatchInitialized

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.util.flowcontrol.Assumptions]

theorem flowcontrol.WatchInitialized.wp_proof
    (wp_from : flowcontrol.initializationSignalFrom.spec (GF := GF) (hG := hG)) :
    flowcontrol.WatchInitialized.spec (GF := GF) (hG := hG) := by
  intro ci
  wp_start as #Hv
  wp_auto
  wp_apply wp_from ci $$ [] as %s %ok %hok
  · iframe #
  subst hok
  wp_auto
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
