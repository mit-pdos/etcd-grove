/-
Package initialization of `k8s_io.api.apps.v1`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.k8s_io.client_go.Base
public import Proof.k8s_io.api.core.v1.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.util.intstr.Init
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
namespace k8s_io.api.apps.v1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.api.apps.v1`'s untranslated variable initializers run.**
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
        map_ControllerRevision.init,
        map_ControllerRevisionList.init,
        map_DaemonSet.init,
        map_DaemonSetCondition.init,
        map_DaemonSetList.init,
        map_DaemonSetSpec.init,
        map_DaemonSetStatus.init,
        map_DaemonSetUpdateStrategy.init,
        map_Deployment.init,
        map_DeploymentCondition.init,
        map_DeploymentList.init,
        map_DeploymentSpec.init,
        map_DeploymentStatus.init,
        map_DeploymentStrategy.init,
        map_ReplicaSet.init,
        map_ReplicaSetCondition.init,
        map_ReplicaSetList.init,
        map_ReplicaSetSpec.init,
        map_ReplicaSetStatus.init,
        map_RollingUpdateDaemonSet.init,
        map_RollingUpdateDeployment.init,
        map_RollingUpdateStatefulSetStrategy.init,
        map_StatefulSet.init,
        map_StatefulSetCondition.init,
        map_StatefulSetList.init,
        map_StatefulSetOrdinals.init,
        map_StatefulSetPersistentVolumeClaimRetentionPolicy.init,
        map_StatefulSetSpec.init,
        map_StatefulSetStatus.init,
        map_StatefulSetUpdateStrategy.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end k8s_io.api.apps.v1
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.api.apps.v1.Assumptions]

namespace k8s_io.api.apps.v1

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.apps.v1 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.apps.v1 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.intstr.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.k8s_io.api.core.v1.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk ErrInvalidLengthGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrIntOverflowGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnexpectedEndOfGroupGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeGroupVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk localSchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk AddToScheme.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ControllerRevision.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ControllerRevisionList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSet.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetUpdateStrategy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Deployment.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentStrategy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSet.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSetCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSetList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSetSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSetStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RollingUpdateDaemonSet.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RollingUpdateDeployment.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RollingUpdateStatefulSetStrategy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatefulSet.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatefulSetCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatefulSetList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatefulSetOrdinals.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatefulSetPersistentVolumeClaimRetentionPolicy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatefulSetSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatefulSetStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatefulSetUpdateStrategy.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.apps.v1 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.apps.v1 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.api.apps.v1

end init

end Perennial
