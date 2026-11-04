/-
Package initialization of `k8s_io.api.autoscaling.v1`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Base
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace k8s_io.api.autoscaling.v1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.api.autoscaling.v1`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrInvalidLengthGenerated.init,
        ErrIntOverflowGenerated.init,
        ErrUnexpectedEndOfGroupGenerated.init,
        SchemeGroupVersion.init,
        SchemeBuilder.init,
        localSchemeBuilder.init,
        AddToScheme.init,
        map_ContainerResourceMetricSource.init,
        map_ContainerResourceMetricStatus.init,
        map_CrossVersionObjectReference.init,
        map_ExternalMetricSource.init,
        map_ExternalMetricStatus.init,
        map_HorizontalPodAutoscaler.init,
        map_HorizontalPodAutoscalerCondition.init,
        map_HorizontalPodAutoscalerList.init,
        map_HorizontalPodAutoscalerSpec.init,
        map_HorizontalPodAutoscalerStatus.init,
        map_MetricSpec.init,
        map_MetricStatus.init,
        map_ObjectMetricSource.init,
        map_ObjectMetricStatus.init,
        map_PodsMetricSource.init,
        map_PodsMetricStatus.init,
        map_ResourceMetricSource.init,
        map_ResourceMetricStatus.init,
        map_Scale.init,
        map_ScaleSpec.init,
        map_ScaleStatus.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end k8s_io.api.autoscaling.v1
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.api.autoscaling.v1.Assumptions]

namespace k8s_io.api.autoscaling.v1

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.autoscaling.v1 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.autoscaling.v1 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk ErrInvalidLengthGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrIntOverflowGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnexpectedEndOfGroupGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeGroupVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk localSchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk AddToScheme.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerResourceMetricSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerResourceMetricStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_CrossVersionObjectReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ExternalMetricSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ExternalMetricStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HorizontalPodAutoscaler.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HorizontalPodAutoscalerCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HorizontalPodAutoscalerList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HorizontalPodAutoscalerSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HorizontalPodAutoscalerStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_MetricSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_MetricStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ObjectMetricSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ObjectMetricStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodsMetricSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodsMetricStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceMetricSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceMetricStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Scale.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ScaleSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ScaleStatus.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.autoscaling.v1 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.autoscaling.v1 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.api.autoscaling.v1

end init

end Perennial
