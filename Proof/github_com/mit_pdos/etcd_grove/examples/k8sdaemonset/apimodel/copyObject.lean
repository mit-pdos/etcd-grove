/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/copyObject.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject
public import Spec.k8s_io.api.core.v1.Pod__DeepCopyObject
public import Spec.k8s_io.api.core.v1.Node__DeepCopyObject
public import Spec.k8s_io.api.apps.v1.DaemonSet__DeepCopyObject
public import Spec.k8s_io.api.apps.v1.ControllerRevision__DeepCopyObject

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

/-- The API types' pointers implement `object` (their method sets, which include
`metav1.Object`'s methods promoted from the embedded `ObjectMeta`). -/
private theorem pod_implements_object :
    go.typeSetContains (go.GoType.PointerType k8s_io.api.core.v1.Pod.ty) apimodel.object.ty = true := by
  go_type_set

/-- As `pod_implements_object`. -/
private theorem node_implements_object :
    go.typeSetContains (go.GoType.PointerType k8s_io.api.core.v1.Node.ty) apimodel.object.ty = true := by
  go_type_set

/-- As `pod_implements_object`. -/
private theorem ds_implements_object :
    go.typeSetContains (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) apimodel.object.ty = true := by
  go_type_set

/-- As `pod_implements_object`. -/
private theorem cr_implements_object :
    go.typeSetContains (go.GoType.PointerType k8s_io.api.apps.v1.ControllerRevision.ty) apimodel.object.ty = true := by
  go_type_set

/-- `o.DeepCopyObject().(object)`: the copy is of `o`'s type, whose method set includes `object`'s
(`runtime.Object`'s and `metav1.Object`'s, promoted from the embedded `ObjectMeta`), so the
assertion succeeds. -/
theorem copyObject.wp_proof
    (wp_Pod : corev1.Pod.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_Node : corev1.Node.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_DaemonSet : appsv1.DaemonSet.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_ControllerRevision : appsv1.ControllerRevision.DeepCopyObject.spec (GF := GF) (hG := hG)) :
    copyObject.spec (GF := GF) (hG := hG) := by
  intro _ o dq ob
  wp_start as Ho
  cases ob with
  | pod d =>
    simp only [objAt, podAt]
    icases Ho with ⟨%l, %ho, %v, Hl, Hown⟩
    subst ho
    wp_auto
    wp_apply wp_Pod $$ [$Hl $Hown] as %l' %v' ⟨Hl, Hown, Hl', Hown'⟩
    simp only [pod_implements_object, ite_true]
    wp_auto
    iapply HΦ
    isplitl [Hl Hown]
    · iexists l; isplitr; · ipureintro; rfl
      iexists v; iframe
    · iexists l'; isplitr; · ipureintro; rfl
      iexists v'; iframe
  | node d =>
    simp only [objAt, nodeAt]
    icases Ho with ⟨%l, %ho, %v, Hl, Hown⟩
    subst ho
    wp_auto
    wp_apply wp_Node $$ [$Hl $Hown] as %l' %v' ⟨Hl, Hown, Hl', Hown'⟩
    simp only [node_implements_object, ite_true]
    wp_auto
    iapply HΦ
    isplitl [Hl Hown]
    · iexists l; isplitr; · ipureintro; rfl
      iexists v; iframe
    · iexists l'; isplitr; · ipureintro; rfl
      iexists v'; iframe
  | ds d =>
    simp only [objAt, dsAt]
    icases Ho with ⟨%l, %ho, %v, Hl, Hown⟩
    subst ho
    wp_auto
    wp_apply wp_DaemonSet $$ [$Hl $Hown] as %l' %v' ⟨Hl, Hown, Hl', Hown'⟩
    simp only [ds_implements_object, ite_true]
    wp_auto
    iapply HΦ
    isplitl [Hl Hown]
    · iexists l; isplitr; · ipureintro; rfl
      iexists v; iframe
    · iexists l'; isplitr; · ipureintro; rfl
      iexists v'; iframe
  | cr d =>
    simp only [objAt, crAt]
    icases Ho with ⟨%l, %ho, %v, Hl, Hown⟩
    subst ho
    wp_auto
    wp_apply wp_ControllerRevision $$ [$Hl $Hown] as %l' %v' ⟨Hl, Hown, Hl', Hown'⟩
    simp only [cr_implements_object, ite_true]
    wp_auto
    iapply HΦ
    isplitl [Hl Hown]
    · iexists l; isplitr; · ipureintro; rfl
      iexists v; iframe
    · iexists l'; isplitr; · ipureintro; rfl
      iexists v'; iframe

end proof

end apimodel
end EtcdGrove
end Perennial
