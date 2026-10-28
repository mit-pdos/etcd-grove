/-
**More lenses for the pod control** (`GetPodFromTemplate` and its helpers read a pod template's
labels, annotations, finalizers and spec; `validateControllerRef` an owner reference). Lean-first.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.PodLens
public import Proof.k8s_io.kubernetes.pkg.controller.PodControlDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [core_sem : k8s_io.api.core.v1.Assumptions]
variable [meta_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

/-- **A pod template's two fields**, read off its deep ownership, and put back. -/
theorem tmplAt_fields (tp : Loc) (dq : DFrac) (t : kd.core.PodTemplateSpec) :
    tmplAt (GF := GF) tp dq t ⊢ ∃ (vm : k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta)
      (vs : k8s_io.api.core.v1.PodSpec),
      tp.[k8s_io.api.core.v1.PodTemplateSpec, go!"ObjectMeta"] ↦{dq} vm ∗
      kd.meta.ObjectMeta.own vm dq t.ObjectMeta' ∗
      tp.[k8s_io.api.core.v1.PodTemplateSpec, go!"Spec"] ↦{dq} vs ∗
      kd.core.PodSpec.own vs dq t.Spec' ∗
      (tp.[k8s_io.api.core.v1.PodTemplateSpec, go!"ObjectMeta"] ↦{dq} vm -∗
        kd.meta.ObjectMeta.own vm dq t.ObjectMeta' -∗
        tp.[k8s_io.api.core.v1.PodTemplateSpec, go!"Spec"] ↦{dq} vs -∗
        kd.core.PodSpec.own vs dq t.Spec' -∗ tmplAt tp dq t) := by
  unfold tmplAt
  iintro ⟨%v, Hl, Hd⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  iunfold kd.core.PodTemplateSpec.own at Hd
  icases Hd with ⟨DObjectMeta, DSpec⟩
  iexists v.ObjectMeta', v.Spec'
  iframe ObjectMeta DObjectMeta Spec DSpec
  iintro ObjectMeta DObjectMeta Spec DSpec
  iexists v
  isplitl [ObjectMeta Spec]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · unfold kd.core.PodTemplateSpec.own
    simp only [named]
    iframe

end lemmas

end dsctl
end EtcdGrove
end Perennial
